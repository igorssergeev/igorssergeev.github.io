/-
# Theorem (full form): self-contained Lean formalisation

This single file contains a complete, `sorry`-free Lean formalisation of the Theorem 1 
stating that the set `H[n,k]` can be computed in polynomial time on the
integer random-access machine used in the paper.

## Main statements

* `BkSet.RAM.theorem1_full` — Theorem 1 in full: the merged program `Th1prog n` halts within
  `O(n^4 + n r^2)` steps, writes the canonical exponents `h_i` of `H[n,k]` and keeps every
  register inside `-1 .. 2^(2r) + O(1)` throughout (`r = BkSet.rOf n k`).
* `BkSet.RAM.theorem1_amp`, `BkSet.RAM.theorem1_amp_n` — the amplitude clause on its own, in
  the paper's `2^(2r) + O(1)` and `2^(2r) + O(n)` shapes.
* `BkSet.RAM.lemma1`, `BkSet.RAM.lemma1_amp` — Lemma 1 (the `O(r^2)` discrete logarithm).
* `BkSet.main_lemma` — `H[n,k]` is a `B_k`-sequence.

All of them depend only on the three standard axioms `propext`, `Classical.choice`,
`Quot.sound` (in particular there is no `sorryAx`).
-/
import Mathlib

-- The next commands only silence cosmetic linters inherited from the original modules
-- (deprecated Mathlib names, unused `simp` arguments, ...); they do not affect any proof.
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false


-- ===============================================================================================
-- ============  Section copied verbatim from H-is-Bk-set.lean  =====================================
-- ===============================================================================================

section

/-
# `H[n,k]` is a `B_k`-sequence in `ZMod (2^(r-2))`

Let `k >= 2` and `r = 1 + ceil(k * log_2 p_n)`, where `p_1, p_2, ...` are the odd
primes in increasing order, so that `p_n` is the `n`-th odd prime (in the file,
`oddPrime (n-1)`). For each `i` write `p_i = +- 5 ^ h_i (mod 2^r)` with
`0 <= h_i < 2^(r-2)`; such an `h_i` exists and is unique because the unit group
`(ZMod (2^r))^x` is isomorphic to `<-1> x <5>` (via `reprMap`). The lemma asserts
that the set `H[n,k] = { h_i | i = 1, ..., n }` is a `B_k`-sequence in
`ZMod (2^(r-2))`, i.e. that all `k`-fold sums of its elements are distinct.

## Main results

* `BkSet.main_lemma` : `IsBkSeq k (Hset n k hk)` -- the lemma.
* `BkSet.core` : distinct `k`-multisets have distinct sums of `h`-values.
* `BkSet.reprMap_bijective` : `(ZMod (2^r))^x ~ Fin 2 x Fin (2^(r-2))`, `(j,h) |-> (-1)^j * 5^h`.
* `BkSet.Pprod_injective` : a product of (distinct) odd primes determines its multiset.
-/

open Nat

namespace BkSet

noncomputable section

/-! ## Part 1: the `±5^h` structure of `(ZMod (2^r))ˣ` -/

def fiveUnit (r : ℕ) : (ZMod (2^r))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right r (by decide))

theorem four_dvd_two_pow (r : ℕ) (hr : 2 ≤ r) : 4 ∣ 2^r := by
  rw [show (4:ℕ) = 2^2 by norm_num]
  exact pow_dvd_pow 2 hr

theorem orderOf_five (r : ℕ) (hr : 2 ≤ r) : orderOf (fiveUnit r) = 2^(r-2) := by
  have h := ZMod.orderOf_five (r - 2)
  rw [show r - 2 + 2 = r by omega] at h
  rw [← orderOf_units]
  simp only [fiveUnit, ZMod.coe_unitOfCoprime]
  exact h

theorem unitsMap_five (r : ℕ) {h : 4 ∣ 2^r} :
    ZMod.unitsMap h (fiveUnit r) = 1 := by
  apply Units.ext
  rw [ZMod.unitsMap_val, Units.val_one, fiveUnit, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]
  decide

theorem unitsMap_negOne (r : ℕ) {h : 4 ∣ 2^r} :
    ZMod.unitsMap h (-1 : (ZMod (2^r))ˣ) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one,
    ZMod.cast_neg h, ZMod.cast_one h]

def reprMap (r : ℕ) : Fin 2 × Fin (2^(r-2)) → (ZMod (2^r))ˣ :=
  fun p => (-1 : (ZMod (2^r))ˣ)^(p.1:ℕ) * (fiveUnit r)^(p.2:ℕ)

theorem reprMap_injective (r : ℕ) (hr : 2 ≤ r) : Function.Injective (reprMap r) := by
  rintro ⟨a, h⟩ ⟨b, h'⟩ hpq
  have h1 : (-1 : (ZMod 4)ˣ)^(a:ℕ) = (-1 : (ZMod 4)ˣ)^(b:ℕ) := by
    have hmap := congrArg (ZMod.unitsMap (four_dvd_two_pow r hr)) hpq
    simp only [reprMap, map_mul, map_pow, unitsMap_five, unitsMap_negOne, one_pow, mul_one] at hmap
    simpa using hmap
  have hab : a = b := by
    revert h1; fin_cases a <;> fin_cases b <;> decide
  have hh : h = h' := by
    have h5 : (fiveUnit r)^(h:ℕ) = (fiveUnit r)^(h':ℕ) := by
      have hthis := hpq
      simp only [reprMap] at hthis
      rw [hab] at hthis
      exact mul_left_cancel hthis
    have hmod : (h:ℕ) ≡ (h':ℕ) [MOD 2^(r-2)] := by
      have := pow_eq_pow_iff_modEq.mp h5
      rwa [orderOf_five r hr] at this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod h.isLt h'.isLt)
  exact Prod.ext hab hh

theorem reprMap_bijective (r : ℕ) (hr : 2 ≤ r) : Function.Bijective (reprMap r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨reprMap_injective r hr, ?_⟩
  haveI : NeZero (2^r) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2^r))ˣ = 2 * 2^(r-2) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    rw [show (2:ℕ) - 1 = 1 by norm_num, mul_one]
    rw [show 2^(r-1) = 2^(r-2) * 2 by
          rw [show r-1 = (r-2)+1 by omega, pow_add, pow_one], mul_comm]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [hcard]

theorem reprMap_surjective (r : ℕ) (hr : 2 ≤ r) : Function.Surjective (reprMap r) :=
  (reprMap_bijective r hr).2

/-! ## Part 2: odd primes -/

def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i+1)

theorem oddPrime_prime (i : ℕ) : (oddPrime i).Prime := Nat.prime_nth_prime (i+1)

theorem three_le_oddPrime (i : ℕ) : 3 ≤ oddPrime i := by
  have h := Nat.add_two_le_nth_prime (i+1)
  simp only [oddPrime]; omega

theorem oddPrime_odd (i : ℕ) : Odd (oddPrime i) :=
  (oddPrime_prime i).odd_of_ne_two (by have := three_le_oddPrime i; omega)

theorem oddPrime_strictMono : StrictMono oddPrime := by
  intro a b hab
  simp only [oddPrime]
  exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr (Nat.succ_lt_succ hab)

theorem oddPrime_injective : Function.Injective oddPrime := oddPrime_strictMono.injective

theorem oddPrime_le {i n : ℕ} (h : i < n) : oddPrime i ≤ oddPrime (n-1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  · exact oddPrime_strictMono.monotone (by omega)

def oddPrimeUnit (r i : ℕ) : (ZMod (2^r))ˣ :=
  ZMod.unitOfCoprime (oddPrime i)
    (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr (oddPrime_odd i)))

theorem oddPrimeUnit_coe (r i : ℕ) :
    ((oddPrimeUnit r i : (ZMod (2^r))ˣ) : ZMod (2^r)) = oddPrime i :=
  ZMod.coe_unitOfCoprime _ _

theorem factorization_oddPrime_self (i : ℕ) :
    (oddPrime i).factorization (oddPrime i) = 1 :=
  (oddPrime_prime i).factorization_self

theorem factorization_oddPrime_ne {a b : ℕ} (h : a ≠ b) :
    (oddPrime a).factorization (oddPrime b) = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have heq : oddPrime b = oddPrime a :=
    (Nat.prime_dvd_prime_iff_eq (oddPrime_prime b) (oddPrime_prime a)).mp hd
  exact h (oddPrime_injective heq).symm

end
end BkSet

namespace BkSet

noncomputable section

noncomputable def reprData (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin 2 × Fin (2^(r-2)) :=
  Classical.choose (reprMap_surjective r hr (oddPrimeUnit r i))

theorem reprData_spec (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    reprMap r (reprData r hr i) = oddPrimeUnit r i :=
  Classical.choose_spec (reprMap_surjective r hr (oddPrimeUnit r i))

def jj (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin 2 := (reprData r hr i).1
def hh (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin (2^(r-2)) := (reprData r hr i).2

theorem reprData_eq (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    reprData r hr i = (jj r hr i, hh r hr i) := rfl

theorem oddPrime_repr (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    (oddPrime i : ZMod (2^r)) = (-1)^(jj r hr i : ℕ) * (5 : ZMod (2^r))^((hh r hr i : ℕ)) := by
  have h := congrArg (fun u : (ZMod (2^r))ˣ => (u : ZMod (2^r))) (reprData_spec r hr i)
  rw [reprData_eq] at h
  simp only [reprMap, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    oddPrimeUnit_coe] at h
  exact h.symm

end
end BkSet

namespace BkSet

noncomputable section

def hz (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : ZMod (2^(r-2)) := (hh r hr i : ℕ)

def jsum (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) : ℕ := (a.map (fun i => (jj r hr i : ℕ))).sum
def hsum (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) : ℕ := (a.map (fun i => (hh r hr i : ℕ))).sum
def Pprod (a : Multiset ℕ) : ℕ := (a.map oddPrime).prod

theorem cast_Pprod (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) :
    ((Pprod a : ℕ) : ZMod (2^r)) = (-1)^(jsum r hr a) * (5 : ZMod (2^r))^(hsum r hr a) := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod, jsum, hsum]
  | cons i a ih =>
    have hcast : ((Pprod (i ::ₘ a) : ℕ) : ZMod (2^r))
        = (oddPrime i : ZMod (2^r)) * ((Pprod a : ℕ) : ZMod (2^r)) := by
      simp only [Pprod, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul]
    rw [hcast, oddPrime_repr r hr i, ih]
    simp only [jsum, hsum, Multiset.map_cons, Multiset.sum_cons]
    rw [pow_add, pow_add]
    ring

end
end BkSet

namespace BkSet

noncomputable section

theorem Pprod_pos (a : Multiset ℕ) : 0 < Pprod a := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod]
  | cons i a ih =>
      simp only [Pprod, Multiset.map_cons, Multiset.prod_cons]
      exact Nat.mul_pos (oddPrime_prime i).pos ih

theorem factorization_Pprod (a : Multiset ℕ) (j : ℕ) :
    (Pprod a).factorization (oddPrime j) = a.count j := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod]
  | cons i a ih =>
      have h1 : Pprod (i ::ₘ a) = oddPrime i * Pprod a := by
        simp only [Pprod, Multiset.map_cons, Multiset.prod_cons]
      rw [h1, Nat.factorization_mul (oddPrime_prime i).ne_zero (Pprod_pos a).ne']
      simp only [Finsupp.add_apply]
      rcases eq_or_ne i j with h | h
      · subst h
        rw [factorization_oddPrime_self, ih, Multiset.count_cons_self]
        omega
      · rw [factorization_oddPrime_ne h, ih, Multiset.count_cons_of_ne h.symm]
        omega

theorem Pprod_injective {a b : Multiset ℕ} (h : Pprod a = Pprod b) : a = b := by
  apply Multiset.ext.mpr
  intro j
  have := congrArg (fun x : ℕ => x.factorization (oddPrime j)) h
  simpa only [factorization_Pprod] using this

theorem Pprod_bound {n k : ℕ} (a : Multiset ℕ) (ha : a.card ≤ k)
    (hall : ∀ i ∈ a, i < n) : Pprod a ≤ oddPrime (n-1)^k := by
  have key : ∀ a : Multiset ℕ, (∀ i ∈ a, i < n) → Pprod a ≤ oddPrime (n-1)^a.card := by
    intro a
    induction a using Multiset.induction_on with
    | empty => intro _; simp [Pprod]
    | cons i a ih =>
        intro h
        have hi : oddPrime i ≤ oddPrime (n-1) := oddPrime_le (h i (by simp))
        have hrec : Pprod a ≤ oddPrime (n-1)^a.card := ih (fun j hj => h j (by simp [hj]))
        simp only [Pprod, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons] at hrec ⊢
        calc oddPrime i * (a.map oddPrime).prod
            ≤ oddPrime (n-1) * oddPrime (n-1)^a.card := Nat.mul_le_mul hi hrec
          _ = oddPrime (n-1) ^ (a.card + 1) := by rw [pow_succ]; ring
  calc Pprod a ≤ oddPrime (n-1)^a.card := key a hall
    _ ≤ oddPrime (n-1)^k := Nat.pow_le_pow_right (by have := three_le_oddPrime (n-1); omega) ha

end
end BkSet

namespace BkSet

noncomputable section

theorem cast_sum_map {N : ℕ} (a : Multiset ℕ) (f : ℕ → ℕ) :
    (a.map (fun i => (f i : ZMod N))).sum = ((a.map f).sum : ZMod N) := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons i a ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ih,
        Nat.cast_add]

theorem hsum_hz (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) :
    (a.map (hz r hr)).sum = (hsum r hr a : ZMod (2^(r-2))) := by
  exact cast_sum_map a (fun i => (hh r hr i : ℕ))

theorem core (r : ℕ) (hr : 2 ≤ r) (n k : ℕ)
    (hbound : oddPrime (n-1)^k < 2^(r-1))
    (a b : Multiset ℕ) (ha : ∀ i ∈ a, i < n) (hb : ∀ j ∈ b, j < n)
    (hca : a.card ≤ k) (hcb : b.card ≤ k)
    (hsum_eq : (a.map (hz r hr)).sum = (b.map (hz r hr)).sum) : a = b := by
  have hmod : hsum r hr a ≡ hsum r hr b [MOD 2^(r-2)] := by
    have h2 := hsum_eq
    rw [hsum_hz r hr a, hsum_hz r hr b] at h2
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  have hfive : (fiveUnit r)^(hsum r hr a) = (fiveUnit r)^(hsum r hr b) := by
    rw [pow_eq_pow_iff_modEq, orderOf_five r hr]; exact hmod
  have h5 : (5 : ZMod (2^r))^(hsum r hr a) = (5 : ZMod (2^r))^(hsum r hr b) := by
    have huu := congrArg (fun u : (ZMod (2^r))ˣ => (u : ZMod (2^r))) hfive
    simp only [Units.val_pow_eq_pow_val] at huu
    rwa [show ((fiveUnit r : (ZMod (2^r))ˣ) : ZMod (2^r)) = 5 from
      ZMod.coe_unitOfCoprime 5 _] at huu
  have hpa : (Pprod a : ZMod (2^r)) = (-1)^(jsum r hr a) * (5 : ZMod (2^r))^(hsum r hr b) := by
    rw [cast_Pprod r hr a, h5]
  have hpb : (Pprod b : ZMod (2^r)) = (-1)^(jsum r hr b) * (5 : ZMod (2^r))^(hsum r hr b) :=
    cast_Pprod r hr b
  have h2le : 2^(r-1) ≤ 2^r := by
    rw [show r = (r-1)+1 by omega, pow_succ']
    exact Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)
  have hba : Pprod a < 2^(r-1) := lt_of_le_of_lt (Pprod_bound a hca ha) hbound
  have hbb : Pprod b < 2^(r-1) := lt_of_le_of_lt (Pprod_bound b hcb hb) hbound
  have hlt_a : Pprod a < 2^r := lt_of_lt_of_le hba h2le
  have hlt_b : Pprod b < 2^r := lt_of_lt_of_le hbb h2le
  have h2r : 2^(r-1) + 2^(r-1) = 2^r := by
    rw [← two_mul, show (2:ℕ) * 2^(r-1) = 2^((r-1)+1) by rw [pow_succ']]
    congr 1; omega
  have hsum_lt : Pprod a + Pprod b < 2^r := by
    have := Nat.add_lt_add hba hbb; rwa [h2r] at this
  have eqcase : ((Pprod a : ℕ) : ZMod (2^r)) = ((Pprod b : ℕ) : ZMod (2^r)) → a = b := by
    intro heq
    exact Pprod_injective
      (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).mp heq) hlt_a hlt_b)
  have negcase : ((Pprod a : ℕ) : ZMod (2^r)) = -((Pprod b : ℕ) : ZMod (2^r)) → a = b := by
    intro heq
    exfalso
    have h0 : ((Pprod a + Pprod b : ℕ) : ZMod (2^r)) = 0 := by
      rw [Nat.cast_add, heq, neg_add_cancel]
    have hdvd : 2^r ∣ Pprod a + Pprod b := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hpos : 0 < Pprod a + Pprod b := Nat.add_pos_left (Pprod_pos a) _
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hsum_lt)
  rcases Nat.even_or_odd (jsum r hr a) with hae | hao <;>
    rcases Nat.even_or_odd (jsum r hr b) with hbe | hbo
  · rw [hae.neg_one_pow, one_mul] at hpa
    rw [hbe.neg_one_pow, one_mul] at hpb
    exact eqcase (by rw [hpa, hpb])
  · rw [hae.neg_one_pow, one_mul] at hpa
    rw [hbo.neg_one_pow, neg_one_mul] at hpb
    exact negcase (by rw [hpa, hpb, neg_neg])
  · rw [hao.neg_one_pow, neg_one_mul] at hpa
    rw [hbe.neg_one_pow, one_mul] at hpb
    exact negcase (by rw [hpa, hpb])
  · rw [hao.neg_one_pow, neg_one_mul] at hpa
    rw [hbo.neg_one_pow, neg_one_mul] at hpb
    exact eqcase (by rw [hpa, hpb])

end
end BkSet

namespace BkSet

noncomputable section

def rOf (n k : ℕ) : ℕ :=
  1 + Nat.ceil ((k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ))

theorem rOf_sub (n k : ℕ) :
    rOf n k - 1 = Nat.ceil ((k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ)) := by
  rw [rOf]; omega

theorem rOf_bound (n k : ℕ) (hk : 1 ≤ k) :
    oddPrime (n-1)^k < 2^(rOf n k - 1) := by
  rw [rOf_sub]
  set P : ℕ := oddPrime (n-1) with hP
  set c : ℕ := Nat.ceil ((k:ℝ) * Real.logb 2 ((P:ℕ) : ℝ)) with hc
  have hPodd : Odd P := by rw [hP]; exact oddPrime_odd (n-1)
  have hP3 : 3 ≤ P := by rw [hP]; exact three_le_oddPrime (n-1)
  have hPpos : (0:ℝ) < (P:ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hceil : (k:ℝ) * Real.logb 2 ((P:ℕ):ℝ) ≤ (c:ℝ) := by
    rw [hc]; exact Nat.le_ceil _
  have h2 : ((P:ℝ))^k ≤ (2:ℝ)^c := by
    have key := (Real.rpow_le_rpow_left_iff (show (1:ℝ) < 2 by norm_num)).mpr hceil
    have hkey : (2:ℝ)^((k:ℝ)*Real.logb 2 ((P:ℕ):ℝ)) = (P:ℝ)^k := by
      rw [mul_comm ((k:ℝ)) (Real.logb 2 ((P:ℕ):ℝ)),
        Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num),
        Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hPpos,
        Real.rpow_natCast]
    rw [hkey, Real.rpow_natCast] at key
    exact key
  have hle : P^k ≤ 2^c := by
    have hcast : ((P^k : ℕ) : ℝ) ≤ ((2^c : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_pow]; exact h2
    exact_mod_cast hcast
  have hne : P^k ≠ 2^c := by
    have hodd : Odd (P^k) := hPodd.pow
    intro hcontra
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · rw [hc0, pow_zero] at hcontra
      have : 1 < P^k := one_lt_pow' (by omega) (by omega)
      omega
    · have hev : Even (2^c) := Even.pow_of_ne_zero (even_two) (by omega)
      rw [← hcontra] at hev
      exact (Nat.not_odd_iff_even.mpr hev) hodd
  exact lt_of_le_of_ne hle hne

end
end BkSet

namespace BkSet

noncomputable section

theorem rOf_ge_two (n k : ℕ) (hk : 1 ≤ k) : 2 ≤ rOf n k := by
  rw [rOf]
  have h1P : (1:ℝ) < ((oddPrime (n-1) : ℕ) : ℝ) :=
    by exact_mod_cast (by have := three_le_oddPrime (n-1); omega : 1 < oddPrime (n-1))
  have hlog : (0:ℝ) < Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ) :=
    Real.logb_pos (b := 2) (by norm_num) h1P
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hX : (0:ℝ) < (k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ) := mul_pos hk0 hlog
  have := Nat.one_le_ceil_iff.mpr hX
  omega

/-- A `k`-sum-distinct set. -/
def IsBkSeq {G : Type*} [AddCommMonoid G] (k : ℕ) (B : Finset G) : Prop :=
  ∀ s t : Multiset G, (∀ x ∈ s, x ∈ B) → (∀ x ∈ t, x ∈ B) →
    s.card = k → t.card = k → s.sum = t.sum → s = t

noncomputable def Hz (n k : ℕ) (hk : 2 ≤ k) (i : ℕ) : ZMod (2^(rOf n k - 2)) :=
  hz (rOf n k) (rOf_ge_two n k (le_trans (by norm_num) hk)) i

noncomputable def Hset (n k : ℕ) (hk : 2 ≤ k) : Finset (ZMod (2^(rOf n k - 2))) :=
  (Finset.range n).image (Hz n k hk)

theorem main_lemma (n k : ℕ) (hk : 2 ≤ k) : IsBkSeq k (Hset n k hk) := by
  have hr : 2 ≤ rOf n k := rOf_ge_two n k (le_trans (by norm_num) hk)
  have hbound : oddPrime (n-1)^k < 2^(rOf n k - 1) := rOf_bound n k (le_trans (by norm_num) hk)
  have hzf : ∀ i, hz (rOf n k) hr i = Hz n k hk i := fun i => rfl
  have hinj : ∀ i j, i < n → j < n → Hz n k hk i = Hz n k hk j → i = j := by
    intro i j hi hj hij
    have heq : (({i} : Multiset ℕ).map (hz (rOf n k) hr)).sum
             = (({j} : Multiset ℕ).map (hz (rOf n k) hr)).sum := by
      simpa [hzf] using hij
    have h := core (rOf n k) hr n k hbound {i} {j} (by simp [hi]) (by simp [hj])
        (by simp; omega) (by simp; omega) heq
    simpa using h
  intro s t hs ht hcs hct hsum
  have key : ∀ (u : Multiset (ZMod (2^(rOf n k - 2)))), (∀ x ∈ u, x ∈ Hset n k hk) →
      ∃ a : Multiset ℕ, (∀ i ∈ a, i < n) ∧ a.card = u.card ∧ (a.map (Hz n k hk)) = u := by
    intro u hu
    refine ⟨u.map (fun x => if hx : x ∈ Hset n k hk then
        Classical.choose (Finset.mem_image.mp hx) else 0), ?_, ?_, ?_⟩
    · intro i hi
      rw [Multiset.mem_map] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      show (if hx : x ∈ Hset n k hk then _ else 0) < n
      rw [dif_pos (hu x hx)]
      exact Finset.mem_range.mp (Classical.choose_spec (Finset.mem_image.mp (hu x hx))).1
    · exact Multiset.card_map _ _
    · rw [Multiset.map_map]
      refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
      intro x hx
      show Hz n k hk (if hx : x ∈ Hset n k hk then _ else 0) = x
      rw [dif_pos (hu x hx)]
      exact (Classical.choose_spec (Finset.mem_image.mp (hu x hx))).2
  obtain ⟨a, ha_lt, ha_card, ha_map⟩ := key s hs
  obtain ⟨b, hb_lt, hb_card, hb_map⟩ := key t ht
  have hsum_ab : (a.map (hz (rOf n k) hr)).sum = (b.map (hz (rOf n k) hr)).sum := by
    have hs' : ((a.map (Hz n k hk)).sum) = ((b.map (Hz n k hk)).sum) := by
      rw [ha_map, hb_map]; exact hsum
    simpa [hzf] using hs'
  have hab := core (rOf n k) hr n k hbound a b ha_lt hb_lt
      (by rw [ha_card]; exact hcs.le) (by rw [hb_card]; exact hct.le) hsum_ab
  rw [← ha_map, ← hb_map, hab]

end
end BkSet

end


-- ===============================================================================================
-- ============  Section `PrimeGen` proving that first-n-primes problem is in P  =================
-- ===============================================================================================

section

/-
Copyright (c) 2026 ReasLab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generating the first `n` primes in polynomial time, on a tiny RAM

This section formalises (a) a minimal random-access-machine (RAM) model whose
instructions are exactly the binary integer operations `+ - * / %`, integer
comparisons `>`/`=`, indirect load/store, conditional jumps and `halt`;
(b) the naive trial-division algorithm that enumerates the first `n` primes;
and (c) the theorem that this concrete program halts within `O(n^4)` steps and
writes the first `n` primes to memory.

## Main results

- `BkSet.RAM.prog` : the prime-generating program (a list of instructions).
- `BkSet.RAM.main` : for every `n`, starting from the initial state `s0 n`, the
  machine halts within `700*(n+1)^4 + 100` steps with `mem (BASE + j)`
  equal to the `j`-th prime for every `j < n`.
- `BkSet.RAM.main_bounded` : the same run has a polynomial step bound and additionally
  never computes an integer larger than `p_n + 1 = nth Prime (n-1) + 1`: at every
  intermediate state *every data register* (the candidate `mem 11`, the divisor `mem 12`,
  the flag `mem 13` and the remainder `mem 14`, see `dataRegs`) is at most `p_n + 1`.
  Every computed integer is thus a candidate `k` or a remainder `k % j < k`, and the flag
  stays in `{0,1}`.
- `BkSet.RAM.main_bounded_all` : the *universal* amplitude bound: at every intermediate
  state **every** register (including the auxiliary cells: the counter `mem 10`, the address
  scratch `mem 15`, the constants and the output cells) is at most `p_n + 1001`.

The `O(n^4)` bound uses Chebyshev's explicit lower bound on the prime counting
function (`Chebyshev.pi_ge`) to show the `n`-th prime is at most `8*(n+1)^2`;
the trial-division loop then performs at most `~ p_n^2` operations.
-/


namespace BkSet.RAM


set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

inductive Op where
  | add (d a b : ℕ) | sub (d a b : ℕ) | mul (d a b : ℕ)
  | quo (d a b : ℕ) | rem (d a b : ℕ)
  | load (d a : ℕ) | store (a b : ℕ)
  | jgt (a b L : ℕ) | jeq (a b L : ℕ) | jmp (L : ℕ) | halt
deriving DecidableEq, Repr

structure State where
  pc : ℕ
  mem : ℕ → ℤ

def Op.exec (s : State) : Op → State
  | .add d a b => ⟨s.pc+1, Function.update s.mem d (s.mem a + s.mem b)⟩
  | .sub d a b => ⟨s.pc+1, Function.update s.mem d (s.mem a - s.mem b)⟩
  | .mul d a b => ⟨s.pc+1, Function.update s.mem d (s.mem a * s.mem b)⟩
  | .quo d a b => ⟨s.pc+1, Function.update s.mem d (s.mem a / s.mem b)⟩
  | .rem d a b => ⟨s.pc+1, Function.update s.mem d (s.mem a % s.mem b)⟩
  | .load d a  => ⟨s.pc+1, Function.update s.mem d (s.mem (s.mem a).toNat)⟩
  | .store a b => ⟨s.pc+1, Function.update s.mem ((s.mem a).toNat) (s.mem b)⟩
  | .jgt a b L => ⟨if s.mem a > s.mem b then L else s.pc+1, s.mem⟩
  | .jeq a b L => ⟨if s.mem a = s.mem b then L else s.pc+1, s.mem⟩
  | .jmp L     => ⟨L, s.mem⟩
  | .halt      => s

def prog : List Op :=
  [ Op.add 10 1 1, Op.add 11 3 1, Op.jeq 10 0 19, Op.add 13 2 1, Op.add 12 3 1,
    Op.jeq 12 11 12, Op.rem 14 11 12, Op.jeq 14 1 9, Op.jmp 10, Op.add 13 1 1,
    Op.add 12 12 2, Op.jmp 5, Op.jeq 13 2 14, Op.jmp 17, Op.add 15 4 10,
    Op.store 15 11, Op.add 10 10 2, Op.add 11 11 2, Op.jmp 2, Op.halt ]

def step (s : State) : State :=
  match prog[s.pc]? with
  | some op => op.exec s
  | none => s

def run : ℕ → State → State
  | 0, s => s
  | (k+1), s => step (run k s)

@[simp] theorem run_zero (s : State) : run 0 s = s := rfl
@[simp] theorem run_succ (k : ℕ) (s : State) : run (k+1) s = step (run k s) := rfl
theorem run_add (a b : ℕ) (s : State) : run (a+b) s = run b (run a s) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, run_succ, run_succ, ih]

-- every step lemma, proved by simp over the program list
theorem st0 (mem) : step ⟨0, mem⟩ = ⟨1, Function.update mem 10 (mem 1 + mem 1)⟩ := by simp [step, prog, Op.exec]
theorem st1 (mem) : step ⟨1, mem⟩ = ⟨2, Function.update mem 11 (mem 3 + mem 1)⟩ := by simp [step, prog, Op.exec]
theorem st2eq (mem) (h : mem 10 = mem 0) : step ⟨2, mem⟩ = ⟨19, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st2ne (mem) (h : mem 10 ≠ mem 0) : step ⟨2, mem⟩ = ⟨3, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st3 (mem) : step ⟨3, mem⟩ = ⟨4, Function.update mem 13 (mem 2 + mem 1)⟩ := by simp [step, prog, Op.exec]
theorem st4 (mem) : step ⟨4, mem⟩ = ⟨5, Function.update mem 12 (mem 3 + mem 1)⟩ := by simp [step, prog, Op.exec]
theorem st5eq (mem) (h : mem 12 = mem 11) : step ⟨5, mem⟩ = ⟨12, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st5ne (mem) (h : mem 12 ≠ mem 11) : step ⟨5, mem⟩ = ⟨6, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st6 (mem) : step ⟨6, mem⟩ = ⟨7, Function.update mem 14 (mem 11 % mem 12)⟩ := by simp [step, prog, Op.exec]
theorem st7eq (mem) (h : mem 14 = mem 1) : step ⟨7, mem⟩ = ⟨9, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st7ne (mem) (h : mem 14 ≠ mem 1) : step ⟨7, mem⟩ = ⟨8, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st8 (mem) : step ⟨8, mem⟩ = ⟨10, mem⟩ := by simp [step, prog, Op.exec]
theorem st9 (mem) : step ⟨9, mem⟩ = ⟨10, Function.update mem 13 (mem 1 + mem 1)⟩ := by simp [step, prog, Op.exec]
theorem st10 (mem) : step ⟨10, mem⟩ = ⟨11, Function.update mem 12 (mem 12 + mem 2)⟩ := by simp [step, prog, Op.exec]
theorem st11 (mem) : step ⟨11, mem⟩ = ⟨5, mem⟩ := by simp [step, prog, Op.exec]
theorem st12eq (mem) (h : mem 13 = mem 2) : step ⟨12, mem⟩ = ⟨14, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st12ne (mem) (h : mem 13 ≠ mem 2) : step ⟨12, mem⟩ = ⟨13, mem⟩ := by simp [step, prog, Op.exec, h]
theorem st13 (mem) : step ⟨13, mem⟩ = ⟨17, mem⟩ := by simp [step, prog, Op.exec]
theorem st14 (mem) : step ⟨14, mem⟩ = ⟨15, Function.update mem 15 (mem 4 + mem 10)⟩ := by simp [step, prog, Op.exec]
theorem st15 (mem) : step ⟨15, mem⟩ = ⟨16, Function.update mem (mem 15).toNat (mem 11)⟩ := by simp [step, prog, Op.exec]
theorem st16 (mem) : step ⟨16, mem⟩ = ⟨17, Function.update mem 10 (mem 10 + mem 2)⟩ := by simp [step, prog, Op.exec]
theorem st17 (mem) : step ⟨17, mem⟩ = ⟨18, Function.update mem 11 (mem 11 + mem 2)⟩ := by simp [step, prog, Op.exec]
theorem st18 (mem) : step ⟨18, mem⟩ = ⟨2, mem⟩ := by simp [step, prog, Op.exec]
theorem st19 (mem) : step ⟨19, mem⟩ = ⟨19, mem⟩ := by simp [step, prog, Op.exec]


theorem inner_iter (mem : ℕ → ℤ) (h : mem 12 ≠ mem 11) :
    ∃ mem', run 6 ⟨5, mem⟩ = ⟨5, mem'⟩ ∧
      mem' 12 = mem 12 + mem 2 ∧
      mem' 14 = mem 11 % mem 12 ∧
      mem' 13 = (if mem 11 % mem 12 = mem 1 then mem 1 + mem 1 else mem 13) ∧
      (∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → mem' i = mem i) := by
  by_cases hz : mem 11 % mem 12 = mem 1
  · refine ⟨Function.update (Function.update (Function.update mem 14 (mem 11 % mem 12)) 13 (mem 1 + mem 1)) 12
      ((Function.update (Function.update mem 14 (mem 11 % mem 12)) 13 (mem 1 + mem 1)) 12 + mem 2), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [run_succ, run_zero]
      rw [st5ne _ h, st6, st7eq _ (by simp [Function.update, hz]), st9, st10, st11]
      simp [Function.update]
    · simp [Function.update]
    · simp [Function.update]
    · simp [Function.update, hz]
    · intro i h1 h2 h3; simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · refine ⟨Function.update (Function.update mem 14 (mem 11 % mem 12)) 12
      ((Function.update mem 14 (mem 11 % mem 12)) 12 + mem 2), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [run_succ, run_zero]
      rw [st5ne _ h, st6, st7ne _ (by simp [Function.update, hz]), st8, st10, st11]
      simp [Function.update]
    · simp [Function.update]
    · simp [Function.update]
    · simp [Function.update, hz]
    · intro i h1 h2 h3; simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

lemma int_rem_zero_iff (m d : ℕ) : ((m:ℤ) % (d:ℤ) = 0) ↔ d ∣ m := by
  rw [← Int.natCast_emod m d, Nat.dvd_iff_mod_eq_zero]
  exact Int.ofNat_eq_zero

lemma exists_div_iff (m d : ℕ) (hdm : d < m) :
    (∃ e, d ≤ e ∧ e < m ∧ e ∣ m) ↔ (d ∣ m ∨ ∃ e, d+1 ≤ e ∧ e < m ∧ e ∣ m) := by
  constructor
  · rintro ⟨e, he1, he2, he3⟩
    by_cases hed : e = d
    · exact Or.inl (hed ▸ he3)
    · exact Or.inr ⟨e, by omega, he2, he3⟩
  · rintro (hdvd | ⟨e, he1, he2, he3⟩)
    · exact ⟨d, le_rfl, hdm, hdvd⟩
    · exact ⟨e, by omega, he2, he3⟩

lemma ite_flag (c : Prop) [Decidable c] (f : ℤ) (hf : f = 0 ∨ f = 1) :
    ((if c then (0:ℤ) else f) = 0 ↔ (c ∨ f = 0)) ∧
    ((if c then (0:ℤ) else f) = 0 ∨ (if c then (0:ℤ) else f) = 1) := by
  constructor
  · by_cases hc : c
    · rw [if_pos hc]; simp [hc]
    · rw [if_neg hc]; simp [hc]
  · by_cases hc : c
    · rw [if_pos hc]; left; rfl
    · rw [if_neg hc]; exact hf

-- iterate lemma carrying the monotone flag
theorem inner_iter_flag (mem : ℕ → ℤ) (h : mem 12 ≠ mem 11) (h1 : mem 1 = 0)
    (hf : mem 13 = 0 ∨ mem 13 = 1) :
    ∃ mem', run 6 ⟨5, mem⟩ = ⟨5, mem'⟩ ∧
      (mem' 13 = 0 ↔ (mem 11 % mem 12 = 0 ∨ mem 13 = 0)) ∧
      (mem' 13 = 0 ∨ mem' 13 = 1) ∧
      mem' 12 = mem 12 + mem 2 ∧
      (∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → mem' i = mem i) := by
  obtain ⟨mem', hrun, h12, _h14, h13, hfr⟩ := inner_iter mem h
  refine ⟨mem', hrun, ?_, ?_, h12, hfr⟩
  · rw [h13]
    by_cases hc : mem 11 % mem 12 = mem 1
    · rw [if_pos hc]
      have hz : mem 11 % mem 12 = 0 := by rw [hc, h1]
      rw [show (mem 1 + mem 1 : ℤ) = 0 by rw [h1]; norm_num]
      simp [hz]
    · rw [if_neg hc]
      have hz : mem 11 % mem 12 ≠ 0 := by
        intro hh; exact hc (by rw [hh, h1])
      simp [hz]
  · rw [h13]
    by_cases hc : mem 11 % mem 12 = mem 1
    · rw [if_pos hc]
      rw [show (mem 1 + mem 1 : ℤ) = 0 by rw [h1]; norm_num]; left; rfl
    · rw [if_neg hc]; exact hf

theorem inner_aux (m : ℕ) :
    ∀ k, ∀ d, ∀ mem : ℕ → ℤ, m - d = k → d ≤ m →
      mem 11 = (m:ℤ) → mem 12 = (d:ℤ) → mem 1 = 0 → mem 2 = 1 →
      (mem 13 = 0 ∨ mem 13 = 1) →
      ∃ t ≤ 6*(m-d)+1, ∃ mem', run t ⟨5,mem⟩ = ⟨12,mem'⟩ ∧ mem' 12 = (m:ℤ) ∧
        (mem' 13 = 0 ↔ (mem 13 = 0 ∨ ∃ e, d ≤ e ∧ e < m ∧ e ∣ m)) ∧
        (mem' 13 = 0 ∨ mem' 13 = 1) ∧
        (∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → mem' i = mem i) := by
  intro k
  induction k with
  | zero =>
    intro d mem hk hdm hm hd h1 h2 hf
    have hdm' : d = m := by omega
    refine ⟨1, by omega, mem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [run_succ, run_zero]
      rw [st5eq _ (by rw [hd, hdm', hm])]
    · rw [hd, hdm']
    · have hnone : ¬ (∃ e, d ≤ e ∧ e < m ∧ e ∣ m) := by rintro ⟨e, he1, he2, _⟩; omega
      simp [hnone]
    · exact hf
    · intro i _ _ _; rfl
  | succ k ih =>
    intro d mem hk hdm hm hd h1 h2 hf
    have hlt : d < m := by omega
    have hne : mem 12 ≠ mem 11 := by rw [hd, hm]; exact_mod_cast (ne_of_lt hlt)
    obtain ⟨mem1, hrun1, hiff0, hflag1, h12, hfr⟩ := inner_iter_flag mem hne h1 hf
    have hm1 : mem1 11 = (m:ℤ) := by rw [hfr 11 (by decide) (by decide) (by decide), hm]
    have hd1 : mem1 12 = ((d+1):ℤ) := by rw [h12, hd, h2]
    have h11 : mem1 1 = 0 := by rw [hfr 1 (by decide) (by decide) (by decide), h1]
    have h21 : mem1 2 = 1 := by rw [hfr 2 (by decide) (by decide) (by decide), h2]
    have hflag0d : (mem1 13 = 0 ↔ (d ∣ m ∨ mem 13 = 0)) := by
      rw [hiff0, hm, hd, propext (int_rem_zero_iff m d)]
    have hk' : m - (d+1) = k := by omega
    obtain ⟨t', ht', mem2, hrun2, h12', h13', hf2, hfr2⟩ := ih (d+1) mem1 hk' (by omega) hm1 hd1 h11 h21 hflag1
    refine ⟨6 + t', by omega, mem2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, hrun1, hrun2]
    · exact h12'
    · rw [h13', hflag0d, exists_div_iff m d hlt]; tauto
    · exact hf2
    · intro i hi1 hi2 hi3; rw [hfr2 i hi1 hi2 hi3, hfr i hi1 hi2 hi3]


def BASE : ℕ := 1000
@[simp] theorem BASE_eq : BASE = 1000 := rfl

def Good (n c m : ℕ) (out : ℕ → ℤ) (mem : ℕ → ℤ) : Prop :=
  mem 0 = (n:ℤ) ∧ mem 1 = 0 ∧ mem 2 = 1 ∧ mem 3 = 2 ∧ mem 4 = (BASE:ℤ) ∧
  mem 10 = (c:ℤ) ∧ mem 11 = (m:ℤ) ∧ (∀ j, mem (BASE + j) = out j)

noncomputable def outInf (m : ℕ) : ℕ → ℤ :=
  fun i => if i < Nat.primeCounting' m then (Nat.nth Nat.Prime i : ℤ) else 0

def initMem (n : ℕ) : ℕ → ℤ :=
  fun i => if i = 0 then (n:ℤ) else if i = 2 then 1 else if i = 3 then 2
    else if i = 4 then (BASE:ℤ) else if i = 11 then 2 else 0

def s0 (n : ℕ) : State := ⟨0, initMem n⟩

-- setup: two steps land at pc 2 with count 0, m 2, output empty
theorem setup (n : ℕ) : run 2 (s0 n) = ⟨2, initMem n⟩ := by
  have h1 : (initMem n) 1 = 0 := by simp [initMem]
  have h3 : (initMem n) 3 = 2 := by simp [initMem]
  rw [show (2:ℕ) = 1 + 1 from rfl, run_succ, run_succ, run_zero]
  rw [show step (s0 n) = ⟨1, Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)⟩ from by
        simp [step, prog, Op.exec, s0]]
  rw [show step ⟨1, Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)⟩
        = ⟨2, Function.update (Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)) 11
            ((Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)) 3
             + (Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)) 1)⟩ from by
        simp [step, prog, Op.exec]]
  refine congrArg (fun m => (⟨2, m⟩ : State)) ?_
  funext i
  by_cases hi11 : i = 11 <;> by_cases hi10 : i = 10 <;>
    simp [Function.update_apply, initMem, hi10, hi11]

theorem Good_s0 (n : ℕ) : Good n 0 2 (fun _ => 0) (initMem n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initMem]
  · simp [initMem]
  · simp [initMem]
  · simp [initMem]
  · simp [initMem, BASE]
  · simp [initMem]
  · simp [initMem]
  · intro j
    simp only [initMem]
    rw [if_neg (by rw [BASE]; omega : ¬ (BASE + j = 0)),
        if_neg (by rw [BASE]; omega : ¬ (BASE + j = 2)),
        if_neg (by rw [BASE]; omega : ¬ (BASE + j = 3)),
        if_neg (by rw [BASE]; omega : ¬ (BASE + j = 4)),
        if_neg (by rw [BASE]; omega : ¬ (BASE + j = 11))]




theorem prime_iff_flag (m : ℕ) (hm : 2 ≤ m) (fl : ℤ)
    (h : fl = 0 ↔ ∃ e, 2 ≤ e ∧ e < m ∧ e ∣ m) (h01 : fl = 0 ∨ fl = 1) :
    (fl = 1 ↔ Nat.Prime m) := by
  have hex_iff : (∃ e, 2 ≤ e ∧ e < m ∧ e ∣ m) ↔ (∃ m' : ℕ, m' ∣ m ∧ 2 ≤ m' ∧ m' < m) := by
    constructor
    · rintro ⟨e, he1, he2, he3⟩; exact ⟨e, he3, he1, he2⟩
    · rintro ⟨e, he1, he2, he3⟩; exact ⟨e, he2, he3, he1⟩
  have hne : fl ≠ 0 ↔ Nat.Prime m := by
    constructor
    · intro hh; by_contra hp2
      exact hh (h.mpr (hex_iff.mpr ((Nat.not_prime_iff_exists_dvd_lt hm).mp hp2)))
    · intro hp2 hz
      exact (Nat.not_prime_iff_exists_dvd_lt hm).mpr (hex_iff.mp (h.mp hz)) hp2
  rw [← hne]
  constructor
  · intro hh; rw [hh]; norm_num
  · intro hh; rcases h01 with hz | ho
    · exact (hh hz).elim
    · exact ho





theorem exit_prime (n c m : ℕ) (out : ℕ → ℤ) (mem : ℕ → ℤ)
    (hG : Good n c m out mem) (h13 : mem 13 = 1) :
    ∃ mem', run 6 ⟨12, mem⟩ = ⟨2, mem'⟩ ∧
      Good n (c+1) (m+1) (Function.update out c (m:ℤ)) mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h10, h11, hout⟩ := hG
  have hcond : mem 13 = mem 2 := by rw [h13, h2]
  have hV11 : (Function.update mem 15 (mem 4 + mem 10)) 11 = mem 11 :=
    Function.update_of_ne (by decide) _ _
  have hV15 : (Function.update mem 15 (mem 4 + mem 10)) 15 = mem 4 + mem 10 :=
    Function.update_self _ _ _
  have hADDR : (mem 4 + mem 10).toNat = BASE + c := by
    rw [h4, h10, ← Nat.cast_add, Int.toNat_natCast]
  refine ⟨(run 6 ⟨12, mem⟩).mem, ?_, ?_⟩
  · rw [show (6:ℕ)=5+1 from rfl, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_zero]
    rw [st12eq _ hcond, st14, st15, st16, st17, st18]
  · rw [show (6:ℕ)=5+1 from rfl, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_zero]
    rw [st12eq _ hcond, st14, st15, st16, st17, st18, hV11, hV15, hADDR]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all [Nat.cast_add])
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all [Nat.cast_add])
    · intro j
      have hne11 : ¬ (BASE + j = 11) := by rw [BASE]; omega
      have hne10 : ¬ (BASE + j = 10) := by rw [BASE]; omega
      have hne15 : ¬ (BASE + j = 15) := by rw [BASE]; omega
      have h10b : ¬ ((10:ℕ) = BASE + c) := by rw [BASE]; omega
      have h2b : ¬ ((2:ℕ) = BASE + c) := by rw [BASE]; omega
      have h10c : ¬ ((10:ℕ) = 15) := by omega
      have h2c : ¬ ((2:ℕ) = 15) := by omega
      have haddr : (BASE + j = BASE + c) = (j = c) :=
        propext (by constructor <;> intro h <;> omega)
      simp only [Function.update_apply, hne11, hne10, hne15, hV11, hV15, h10b, h2b, h10c, h2c, haddr]
      by_cases hjc : j = c <;> simp_all

theorem exit_comp (n c m : ℕ) (out : ℕ → ℤ) (mem : ℕ → ℤ)
    (hG : Good n c m out mem) (h13 : mem 13 ≠ mem 2) :
    ∃ mem', run 4 ⟨12, mem⟩ = ⟨2, mem'⟩ ∧ Good n c (m+1) out mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h10, h11, hout⟩ := hG
  refine ⟨(run 4 ⟨12, mem⟩).mem, ?_, ?_⟩
  · rw [show (4:ℕ)=3+1 from rfl, run_succ, run_succ, run_succ, run_succ, run_zero]
    rw [st12ne _ h13, st13, st17, st18]
  · rw [show (4:ℕ)=3+1 from rfl, run_succ, run_succ, run_succ, run_succ, run_zero]
    rw [st12ne _ h13, st13, st17, st18]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all)
    · simp only [Function.update_apply, BASE_eq]; split_ifs <;> (first | omega | simp_all [Nat.cast_add])
    · intro j
      have hne11 : ¬ (1000 + j = 11) := by omega
      simp only [Function.update_apply, hne11, BASE_eq]
      exact hout j


theorem phase (n c m : ℕ) (out : ℕ → ℤ) (mem : ℕ → ℤ) (hc : c < n) (hm : 2 ≤ m)
    (hG : Good n c m out mem) :
    ∃ t ≤ 6*m + 12, ∃ mem', run t ⟨2, mem⟩ = ⟨2, mem'⟩ ∧
      Good n (if Nat.Prime m then c+1 else c) (m+1)
           (if Nat.Prime m then Function.update out c (m:ℤ) else out) mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h10, h11, hout⟩ := hG
  have hne : mem 10 ≠ mem 0 := by rw [h10, h0]; exact_mod_cast (ne_of_lt hc)
  have hE1 : run 3 ⟨2, mem⟩ = ⟨5, Function.update (Function.update mem 13 1) 12 2⟩ := by
    rw [show (3:ℕ)=2+1 from rfl, run_succ, run_succ, run_succ, run_zero]
    rw [st2ne _ hne, st3, st4]
    simp [Function.update_apply, h1, h2, h3]
  obtain ⟨t1, ht1, mem', hrun1, h12', hfl, hfl01, hframe⟩ :=
    inner_aux m (m-2) 2 (Function.update (Function.update mem 13 1) 12 2) rfl (by omega)
      (by simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h11)
      (by rw [Function.update_self]; norm_num)
      (by simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h1)
      (by simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h2)
      (Or.inr (by rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 12), Function.update_self]))
  have hm5_13 : (Function.update (Function.update mem 13 1) 12 2) 13 = 1 := by
    rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 12), Function.update_self]
  have hfl' : mem' 13 = 0 ↔ ∃ e, 2 ≤ e ∧ e < m ∧ e ∣ m := by
    rw [hfl, show ((Function.update (Function.update mem 13 1) 12 2) 13 = (0:ℤ)) = False by
      rw [hm5_13]; norm_num]
    simp
  have hprime : mem' 13 = 1 ↔ Nat.Prime m := prime_iff_flag m hm (mem' 13) hfl' hfl01
  have hG' : Good n c m out mem' := by
    have e0 : mem' 0 = (n:ℤ) := by
      rw [hframe 0 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h0
    have e1 : mem' 1 = 0 := by
      rw [hframe 1 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h1
    have e2 : mem' 2 = 1 := by
      rw [hframe 2 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h2
    have e3 : mem' 3 = 2 := by
      rw [hframe 3 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h3
    have e4 : mem' 4 = (BASE:ℤ) := by
      rw [hframe 4 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h4
    have e10 : mem' 10 = (c:ℤ) := by
      rw [hframe 10 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h10
    have e11 : mem' 11 = (m:ℤ) := by
      rw [hframe 11 (by decide) (by decide) (by decide)]
      simp only [Function.update_apply]; rw [if_neg (by decide), if_neg (by decide)]; exact h11
    have eout : ∀ j, mem' (BASE + j) = out j := by
      intro j
      rw [hframe (BASE + j) (by rw [BASE]; omega) (by rw [BASE]; omega) (by rw [BASE]; omega)]
      simp only [Function.update_apply]
      rw [if_neg (by rw [BASE]; omega), if_neg (by rw [BASE]; omega)]
      exact hout j
    exact ⟨e0, e1, e2, e3, e4, e10, e11, eout⟩
  by_cases hp : Nat.Prime m
  · have h13 : mem' 13 = 1 := hprime.mpr hp
    obtain ⟨mem'', hrun2, hG''⟩ := exit_prime n c m out mem' hG' h13
    refine ⟨3 + t1 + 6, by omega, mem'', ?_, ?_⟩
    · rw [show 3 + t1 + 6 = (3 + t1) + 6 from by ring, run_add, run_add, hE1, hrun1, hrun2]
    · simp only [if_pos hp]; exact hG''
  · have h132 : mem' 2 = 1 := hG'.2.2.1
    have h13 : mem' 13 ≠ mem' 2 := by
      rw [h132]; intro hh; exact hp (hprime.mp hh)
    obtain ⟨mem'', hrun2, hG''⟩ := exit_comp n c m out mem' hG' h13
    refine ⟨3 + t1 + 4, by omega, mem'', ?_, ?_⟩
    · rw [show 3 + t1 + 4 = (3 + t1) + 4 from by ring, run_add, run_add, hE1, hrun1, hrun2]
    · simp only [if_neg hp]; exact hG''

theorem pcs_succ (m : ℕ) :
    Nat.primeCounting' (m+1) = Nat.primeCounting' m + (if Nat.Prime m then 1 else 0) := by
  simp only [Nat.primeCounting', Nat.count_succ]

theorem nth_pc_self {m : ℕ} (hm : Nat.Prime m) : Nat.nth Nat.Prime (Nat.primeCounting' m) = m := by
  simp only [Nat.primeCounting']; exact Nat.nth_count hm

theorem outInf_succ (m : ℕ) :
    outInf (m+1) = (if Nat.Prime m then Function.update (outInf m) (Nat.primeCounting' m) (m:ℤ) else outInf m) := by
  funext i
  by_cases hp : Nat.Prime m
  · rw [if_pos hp]
    simp only [outInf, pcs_succ m, if_pos hp]
    by_cases hi : i = Nat.primeCounting' m
    · subst hi
      rw [if_pos (Nat.lt_succ_self _), Function.update_self, nth_pc_self hp]
    · rw [Function.update_of_ne hi]
      simp only [outInf]
      by_cases hlt : i < Nat.primeCounting' m
      · rw [if_pos (by omega : i < Nat.primeCounting' m + 1), if_pos hlt]
      · rw [if_neg (by omega : ¬ (i < Nat.primeCounting' m + 1)), if_neg hlt]
  · rw [if_neg hp]
    simp only [outInf, pcs_succ m, if_neg hp, add_zero]


open Real in
theorem key (k : ℕ) (hk : 3 ≤ k) :
    (k : ℝ) ≤ (8 * (k:ℝ)^2 * log 2 - log (8 * (k:ℝ)^2 + 1)) / log (8 * (k:ℝ)^2) := by
  set K : ℝ := (k : ℝ) with hKdef
  have hk3 : (3:ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hk
  have hKpos : (0:ℝ) < K := by linarith
  have hlogNpos : (0:ℝ) < log (8 * K^2) := by
    apply Real.log_pos; nlinarith [hk3]
  rw [le_div_iff₀ hlogNpos]
  have hlogN_le : log (8 * K^2) ≤ 3 * log 2 + 2 * log K := by
    have h1 : log (8 * K^2) = log 8 + log (K^2) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    rw [h1, Real.log_pow]
    have h8 : log 8 = 3 * log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h8]; push_cast; linarith
  have hlogK_le : log K ≤ K := by
    have := Real.log_le_sub_one_of_pos hKpos; linarith
  have hnum_le : log (8 * K^2 + 1) ≤ 4 * log 2 + 2 * K := by
    have hle : 8 * K^2 + 1 ≤ 16 * K^2 := by nlinarith [hk3]
    calc log (8 * K^2 + 1) ≤ log (16 * K^2) := Real.log_le_log (by positivity) hle
      _ = log 16 + log (K^2) := by rw [Real.log_mul (by norm_num) (by positivity)]
      _ = 4 * log 2 + 2 * log K := by
            rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
      _ ≤ 4 * log 2 + 2 * K := by linarith [hlogK_le]
  have e1 : 3 ≤ 8 * log 2 - 2 := by nlinarith [Real.log_two_gt_d9]
  have e2 : 3 * log 2 + 2 ≤ 5 := by nlinarith [Real.log_two_lt_d9]
  have e3 : 4 * log 2 ≤ 4 := by nlinarith [Real.log_two_lt_d9]
  have quad : 0 ≤ 3 * K^2 - 5 * K - 4 := by nlinarith [hk3, sq_nonneg (K - 3)]
  have hfin : K * (3 * log 2 + 2 * K) ≤ 8 * K^2 * log 2 - (4 * log 2 + 2 * K) := by
    nlinarith [e1, e2, e3, quad, hKpos, sq_nonneg K]
  calc K * log (8 * K^2) ≤ K * (3 * log 2 + 2 * K) := by nlinarith [hlogN_le, hKpos]
    _ ≤ 8 * K^2 * log 2 - (4 * log 2 + 2 * K) := hfin
    _ ≤ 8 * K^2 * log 2 - log (8 * K^2 + 1) := by linarith [hnum_le]

open Real in
theorem pi_lower (k : ℕ) (hk : 1 ≤ k) : k ≤ Nat.primeCounting (8 * k^2) := by
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · interval_cases k <;> decide
  · have h := Chebyshev.pi_ge (8 * k^2)
    have hkey := key k hge
    have hcast : ((8*k^2 : ℕ) : ℝ) = 8 * (k:ℝ)^2 := by push_cast; ring
    have hkey' : (k:ℝ) ≤ (↑(8*k^2 : ℕ) * log 2 - log (↑(8*k^2 : ℕ) + 1)) / log ↑(8*k^2 : ℕ) := by
      rw [hcast]; exact hkey
    have hcomp : (k:ℝ) ≤ (Nat.primeCounting (8*k^2) : ℝ) := le_trans hkey' h
    exact_mod_cast hcomp

theorem nth_prime_le (n : ℕ) : Nat.nth Nat.Prime n ≤ 8 * (n+1)^2 := by
  have hk : 1 ≤ n + 1 := by omega
  have hpi : n + 1 ≤ Nat.primeCounting (8 * (n+1)^2) := pi_lower (n+1) hk
  have hcount : n + 1 ≤ Nat.count Nat.Prime (8 * (n+1)^2 + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using hpi
  have hiff := Nat.count_le_iff_le_nth (p := Nat.Prime) Nat.infinite_setOfPred_prime
    (a := 8 * (n+1)^2 + 1) (b := n)
  by_contra hlt
  push_neg at hlt
  have := hiff.mpr hlt
  omega



theorem run_upto (n : ℕ) (hn : 1 ≤ n) :
    ∀ m, 2 ≤ m → m ≤ Nat.nth Nat.Prime (n-1) + 1 →
      ∃ t ≤ 6*m*m + 14*m, ∃ mem : ℕ → ℤ, run t ⟨2, initMem n⟩ = ⟨2, mem⟩ ∧
        Good n (Nat.primeCounting' m) m (outInf m) mem := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm2 hmle
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · interval_cases m
      refine ⟨0, by norm_num, initMem n, by rw [run_zero], ?_⟩
      have hπ : Nat.primeCounting' 2 = 0 := by decide
      rw [hπ]
      have hout0 : outInf 2 = (fun _ => 0) := by
        funext i; simp only [outInf, hπ]; simp
      rw [hout0]
      exact Good_s0 n
    · have hprev2 : 2 ≤ m - 1 := by omega
      have hprevle : m - 1 ≤ Nat.nth Nat.Prime (n-1) + 1 := by omega
      obtain ⟨t, ht, mem, hrun, hG⟩ := ih (m-1) (by omega) hprev2 hprevle
      have hc : Nat.primeCounting' (m-1) < n := by
        have hmono : Nat.primeCounting' (m-1) ≤ Nat.primeCounting' (Nat.nth Nat.Prime (n-1)) :=
          Nat.monotone_primeCounting' (by omega)
        rw [Nat.primeCounting'_nth_eq] at hmono
        omega
      obtain ⟨t', ht', mem', hrun', hG'⟩ :=
        phase n (Nat.primeCounting' (m-1)) (m-1) (outInf (m-1)) mem hc (by omega) hG
      have hm1 : m - 1 + 1 = m := by omega
      refine ⟨t + t', ?_, mem', ?_, ?_⟩
      · exact le_trans (add_le_add ht ht') (by nlinarith [hm1, Nat.zero_le (m-1)])
      · rw [run_add, hrun, hrun']
      · rw [show m = m - 1 + 1 from hm1.symm]
        rw [outInf_succ (m-1), pcs_succ (m-1)]
        rw [show Nat.primeCounting' (m-1) + (if Nat.Prime (m-1) then 1 else 0)
              = (if Nat.Prime (m-1) then Nat.primeCounting' (m-1) + 1 else Nat.primeCounting' (m-1)) from by
            by_cases hpc : Nat.Prime (m-1) <;> simp [hpc]]
        exact hG'

theorem main (n : ℕ) :
    ∃ T ≤ 700 * (n+1)^4 + 100, ∃ mem : ℕ → ℤ,
      run T (s0 n) = ⟨19, mem⟩ ∧
      ∀ j, j < n → mem (BASE + j) = (Nat.nth Nat.Prime j : ℤ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨3, by norm_num, initMem 0, ?_, ?_⟩
    · rw [show (3:ℕ)=2+1 from rfl, run_succ, setup 0, st2eq _ (by simp [initMem])]
    · intro j hj; omega
  · have hM : Nat.nth Nat.Prime (n-1) ≤ 8*n^2 := by
      have := nth_prime_le (n-1)
      rwa [Nat.sub_add_cancel hn] at this
    obtain ⟨t, ht, mem, hrun, hG⟩ := run_upto n hn (Nat.nth Nat.Prime (n-1) + 1)
      (by have h := Nat.add_two_le_nth_prime (n-1); omega) (le_refl _)
    obtain ⟨g0, g1, g2, g3, g4, g10, g11, gout⟩ := hG
    have hcount : Nat.primeCounting' (Nat.nth Nat.Prime (n-1) + 1) = n := by
      rw [pcs_succ (Nat.nth Nat.Prime (n-1)), Nat.primeCounting'_nth_eq (n-1)]
      rw [if_pos (Nat.prime_nth_prime (n-1))]
      omega
    refine ⟨t + 3, ?_, mem, ?_, ?_⟩
    · have hM9 : Nat.nth Nat.Prime (n-1) + 1 ≤ 9*n^2 := by nlinarith [hM, hn]
      nlinarith [ht, hM9, hn]
    · rw [show t + 3 = (2 + t) + 1 from by omega, run_add, run_add, setup n, hrun, run_succ, run_zero]
      rw [st2eq _ (by rw [g10, hcount]; exact g0.symm)]
    · intro j hj
      rw [gout j]
      simp only [outInf]
      rw [if_pos (by rw [hcount]; exact hj)]


/-! ### Amplitude bound: no intermediate value exceeds `p_n`

During a trial-division pass the machine tests a candidate `k` (`mem 11`), dividing it by
successive divisors `j` (`mem 12`) with `2 ≤ j < k`, and records the remainder `k % j`
(`mem 14`).  Every integer the machine *computes* as data is therefore either a candidate
`k` or a remainder `k % j < k`; the flag `mem 13` stays in `{0,1}`.  The only value that
ever reaches `p_n + 1` is the candidate counter, bumped once as the last needed prime `p_n`
is stored, right before `halt`. -/

/-- Register-value bound used for the amplitude invariant. -/
def VB (P : ℕ) (mem : ℕ → ℤ) : Prop :=
  mem 11 ≤ (P : ℤ) + 1 ∧ mem 12 ≤ (P : ℤ) ∧ mem 14 ≤ (P : ℤ) ∧
    (0 : ℤ) ≤ mem 14 ∧ (0 : ℤ) ≤ mem 13 ∧ mem 13 ≤ 1

/-- The data registers written during a trial-division pass: the candidate `k` (`mem 11`),
the divisor `j` (`mem 12`), the flag (`mem 13`) and the remainder `k % j` (`mem 14`). -/
def dataRegs : Finset ℕ := {11, 12, 13, 14}

/-- Uniform form of the amplitude bound: every data register is at most `P + 1`.  We no
longer distinguish which register actually reaches `P` and which one reaches `P + 1`. -/
theorem VB_dataRegs (P : ℕ) (mem : ℕ → ℤ) (h : VB P mem) :
    ∀ i ∈ dataRegs, mem i ≤ (P : ℤ) + 1 := by
  obtain ⟨h11, h12, h14, _h14n, _h13n, h13u⟩ := h
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := by exact_mod_cast Nat.zero_le P
  intro i hi
  fin_cases hi
  · exact h11
  · linarith
  · linarith
  · linarith

/-- Concatenation of two run segments, both preserving `VB`. -/
theorem VB_concat (P : ℕ) (s s₁ : State) (a b : ℕ) (h : run a s = s₁)
    (ha : ∀ j ≤ a, ∀ pc ms, run j s = ⟨pc, ms⟩ → VB P ms)
    (hb : ∀ i ≤ b, ∀ pc ms, run i s₁ = ⟨pc, ms⟩ → VB P ms) :
    ∀ j ≤ a + b, ∀ pc ms, run j s = ⟨pc, ms⟩ → VB P ms := by
  intro j hj pc ms hrun
  by_cases hja : j ≤ a
  · exact ha j hja pc ms hrun
  · have hji : j = a + (j - a) := by omega
    have hi : j - a ≤ b := by omega
    rw [hji, run_add, h] at hrun
    exact hb (j - a) hi pc ms hrun

/-- One trial-division pass: six steps from `⟨5, mem⟩` back to `⟨5, mem'⟩`, incrementing the
divisor by one; every intermediate state satisfies `VB P`. -/
theorem inner_iter_vb (P : ℕ) (mem : ℕ → ℤ) (hne : mem 12 ≠ mem 11)
    (h11 : mem 11 ≤ (P : ℤ)) (h2 : (2 : ℤ) ≤ mem 12) (hlt : mem 12 < mem 11)
    (h1c : mem 1 = 0) (h2c : mem 2 = 1)
    (h14 : mem 14 ≤ (P : ℤ)) (h14n : (0 : ℤ) ≤ mem 14)
    (h13n : (0 : ℤ) ≤ mem 13) (h13u : mem 13 ≤ 1) :
    ∃ mem', run 6 ⟨5, mem⟩ = ⟨5, mem'⟩ ∧ mem' 12 = mem 12 + mem 2 ∧ mem' 11 = mem 11 ∧
      mem' 14 ≤ (P : ℤ) ∧ (0 : ℤ) ≤ mem' 14 ∧
      (mem' 13 = 0 ↔ (mem 11 % mem 12 = 0 ∨ mem 13 = 0)) ∧
      (mem' 13 = 0 ∨ mem' 13 = 1) ∧ mem' 1 = mem 1 ∧ mem' 2 = mem 2 ∧
      (∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → mem' i = mem i) ∧
      (∀ j ≤ 6, ∀ pc ms, run j ⟨5, mem⟩ = ⟨pc, ms⟩ → VB P ms) := by
  have hpos : (0 : ℤ) < mem 12 := by linarith
  have hb12 : mem 12 ≤ (P : ℤ) := le_of_lt (lt_of_lt_of_le hlt h11)
  have hA0 : mem 11 % mem 12 ≤ (P : ℤ) :=
    le_of_lt (lt_of_lt_of_le (Int.emod_lt_of_pos _ hpos) hb12)
  have hA0n : (0 : ℤ) ≤ mem 11 % mem 12 := Int.emod_nonneg _ (ne_of_gt hpos)
  have hvbm : VB P mem := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · exact hb12
    · exact h14
    · exact h14n
    · exact h13n
    · exact h13u
  have e1 : run 1 ⟨5, mem⟩ = ⟨6, mem⟩ := by
    simp only [run_succ, run_zero]; rw [st5ne _ hne]
  set A : ℕ → ℤ := Function.update mem 14 (mem 11 % mem 12) with hA
  have hA11 : A 11 = mem 11 := by rw [hA, Function.update_of_ne (by decide : (11:ℕ) ≠ 14)]
  have hA12 : A 12 = mem 12 := by rw [hA, Function.update_of_ne (by decide : (12:ℕ) ≠ 14)]
  have hA13 : A 13 = mem 13 := by rw [hA, Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]
  have hA14 : A 14 = mem 11 % mem 12 := by rw [hA, Function.update_self]
  have hA1 : A 1 = mem 1 := by rw [hA, Function.update_of_ne (by decide : (1:ℕ) ≠ 14)]
  have hA2 : A 2 = mem 2 := by rw [hA, Function.update_of_ne (by decide : (2:ℕ) ≠ 14)]
  have hvA : VB P A := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA11]; linarith
    · rw [hA12]; exact hb12
    · rw [hA14]; exact hA0
    · rw [hA14]; exact hA0n
    · rw [hA13]; exact h13n
    · rw [hA13]; exact h13u
  have e2 : run 2 ⟨5, mem⟩ = ⟨7, A⟩ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, run_succ, e1, st6, hA]
  by_cases hz : mem 11 % mem 12 = mem 1
  · set C : ℕ → ℤ := Function.update A 13 (A 1 + A 1) with hC
    have hC11 : C 11 = mem 11 := by rw [hC, Function.update_of_ne (by decide : (11:ℕ) ≠ 13), hA11]
    have hC12 : C 12 = mem 12 := by rw [hC, Function.update_of_ne (by decide : (12:ℕ) ≠ 13), hA12]
    have hC14 : C 14 = mem 11 % mem 12 := by rw [hC, Function.update_of_ne (by decide : (14:ℕ) ≠ 13), hA14]
    have hC13 : C 13 = 0 := by rw [hC, Function.update_self, hA1, h1c]; norm_num
    have hC1 : C 1 = mem 1 := by rw [hC, Function.update_of_ne (by decide : (1:ℕ) ≠ 13), hA1]
    have hC2 : C 2 = mem 2 := by rw [hC, Function.update_of_ne (by decide : (2:ℕ) ≠ 13), hA2]
    have hvC : VB P C := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hC11]; linarith
      · rw [hC12]; exact hb12
      · rw [hC14]; exact hA0
      · rw [hC14]; exact hA0n
      · simp [hC13]
      · simp [hC13]
    set B : ℕ → ℤ := Function.update C 12 (C 12 + C 2) with hB
    have hB11 : B 11 = mem 11 := by rw [hB, Function.update_of_ne (by decide : (11:ℕ) ≠ 12), hC11]
    have hB12 : B 12 = mem 12 + mem 2 := by rw [hB, Function.update_self, hC12, hC2]
    have hB14 : B 14 = mem 11 % mem 12 := by rw [hB, Function.update_of_ne (by decide : (14:ℕ) ≠ 12), hC14]
    have hB13 : B 13 = 0 := by rw [hB, Function.update_of_ne (by decide : (13:ℕ) ≠ 12), hC13]
    have hB1 : B 1 = mem 1 := by rw [hB, Function.update_of_ne (by decide : (1:ℕ) ≠ 12), hC1]
    have hB2 : B 2 = mem 2 := by rw [hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 12), hC2]
    have hvB : VB P B := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hB11]; linarith
      · rw [hB12, h2c]; linarith
      · rw [hB14]; exact hA0
      · rw [hB14]; exact hA0n
      · simp [hB13]
      · simp [hB13]
    have e3 : run 3 ⟨5, mem⟩ = ⟨9, A⟩ := by
      rw [show (3:ℕ) = 2 + 1 from rfl, run_succ, e2,
          st7eq _ (by rw [hA, Function.update_self, Function.update_of_ne (by decide : (1:ℕ) ≠ 14), hz])]
    have e4 : run 4 ⟨5, mem⟩ = ⟨10, C⟩ := by
      rw [show (4:ℕ) = 3 + 1 from rfl, run_succ, e3, st9, hC]
    have e5 : run 5 ⟨5, mem⟩ = ⟨11, B⟩ := by
      rw [show (5:ℕ) = 4 + 1 from rfl, run_succ, e4, st10, hB]
    have e6 : run 6 ⟨5, mem⟩ = ⟨5, B⟩ := by
      rw [show (6:ℕ) = 5 + 1 from rfl, run_succ, e5, st11]
    have hiffB : (B 13 = 0 ↔ (mem 11 % mem 12 = 0 ∨ mem 13 = 0)) := by
      rw [hB13]; constructor
      · intro _; left; rw [hz, h1c]
      · intro _; rfl
    have hfrB : ∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → B i = mem i := by
      intro i hi1 hi2 hi3
      rw [hB, Function.update_of_ne hi1, hC, Function.update_of_ne hi2, hA, Function.update_of_ne hi3]
    have hbound : ∀ j ≤ 6, ∀ pc ms, run j ⟨5, mem⟩ = ⟨pc, ms⟩ → VB P ms := by
      intro j hj pc ms hrun
      have hj6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hj6 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbm
      · simp only [run_succ, run_zero] at hrun; rw [st5ne _ hne] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbm
      · rw [e2] at hrun; injection hrun with _ hms; rw [← hms]; exact hvA
      · rw [e3] at hrun; injection hrun with _ hms; rw [← hms]; exact hvA
      · rw [e4] at hrun; injection hrun with _ hms; rw [← hms]; exact hvC
      · rw [e5] at hrun; injection hrun with _ hms; rw [← hms]; exact hvB
      · rw [e6] at hrun; injection hrun with _ hms; rw [← hms]; exact hvB
    have hB14a : B 14 ≤ (P : ℤ) := by rw [hB14]; exact hA0
    have hB14b : (0 : ℤ) ≤ B 14 := by rw [hB14]; exact hA0n
    have hB13a : B 13 = 0 ∨ B 13 = 1 := by rw [hB13]; left; rfl
    exact ⟨B, e6, hB12, hB11, hB14a, hB14b, hiffB, hB13a, hB1, hB2, hfrB, hbound⟩
  · set B : ℕ → ℤ := Function.update A 12 (A 12 + A 2) with hB
    have hB11 : B 11 = mem 11 := by rw [hB, Function.update_of_ne (by decide : (11:ℕ) ≠ 12), hA11]
    have hB12 : B 12 = mem 12 + mem 2 := by rw [hB, Function.update_self, hA12, hA2]
    have hB14 : B 14 = mem 11 % mem 12 := by rw [hB, Function.update_of_ne (by decide : (14:ℕ) ≠ 12), hA14]
    have hB13 : B 13 = mem 13 := by rw [hB, Function.update_of_ne (by decide : (13:ℕ) ≠ 12), hA13]
    have hB1 : B 1 = mem 1 := by rw [hB, Function.update_of_ne (by decide : (1:ℕ) ≠ 12), hA1]
    have hB2 : B 2 = mem 2 := by rw [hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 12), hA2]
    have hz0 : mem 11 % mem 12 ≠ 0 := by intro hh; exact hz (by rw [hh, h1c])
    have hvB : VB P B := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hB11]; linarith
      · rw [hB12, h2c]; linarith
      · rw [hB14]; exact hA0
      · rw [hB14]; exact hA0n
      · rw [hB13]; exact h13n
      · rw [hB13]; exact h13u
    have e3 : run 3 ⟨5, mem⟩ = ⟨8, A⟩ := by
      rw [show (3:ℕ) = 2 + 1 from rfl, run_succ, e2,
          st7ne _ (by rw [hA, Function.update_self, Function.update_of_ne (by decide : (1:ℕ) ≠ 14)]; exact hz)]
    have e4 : run 4 ⟨5, mem⟩ = ⟨10, A⟩ := by
      rw [show (4:ℕ) = 3 + 1 from rfl, run_succ, e3, st8]
    have e5 : run 5 ⟨5, mem⟩ = ⟨11, B⟩ := by
      rw [show (5:ℕ) = 4 + 1 from rfl, run_succ, e4, st10, hB]
    have e6 : run 6 ⟨5, mem⟩ = ⟨5, B⟩ := by
      rw [show (6:ℕ) = 5 + 1 from rfl, run_succ, e5, st11]
    have hiffB : (B 13 = 0 ↔ (mem 11 % mem 12 = 0 ∨ mem 13 = 0)) := by
      rw [hB13]; constructor
      · intro h; right; exact h
      · rintro (h | h)
        · exact absurd h hz0
        · exact h
    have hflagB : B 13 = 0 ∨ B 13 = 1 := by rw [hB13]; omega
    have hfrB : ∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → B i = mem i := by
      intro i hi1 hi2 hi3
      rw [hB, Function.update_of_ne hi1, hA, Function.update_of_ne hi3]
    have hbound : ∀ j ≤ 6, ∀ pc ms, run j ⟨5, mem⟩ = ⟨pc, ms⟩ → VB P ms := by
      intro j hj pc ms hrun
      have hj6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hj6 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbm
      · simp only [run_succ, run_zero] at hrun; rw [st5ne _ hne] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbm
      · rw [e2] at hrun; injection hrun with _ hms; rw [← hms]; exact hvA
      · rw [e3] at hrun; injection hrun with _ hms; rw [← hms]; exact hvA
      · rw [e4] at hrun; injection hrun with _ hms; rw [← hms]; exact hvA
      · rw [e5] at hrun; injection hrun with _ hms; rw [← hms]; exact hvB
      · rw [e6] at hrun; injection hrun with _ hms; rw [← hms]; exact hvB
    have hB14a : B 14 ≤ (P : ℤ) := by rw [hB14]; exact hA0
    have hB14b : (0 : ℤ) ≤ B 14 := by rw [hB14]; exact hA0n
    exact ⟨B, e6, hB12, hB11, hB14a, hB14b, hiffB, hflagB, hB1, hB2, hfrB, hbound⟩

/-- The whole inner trial-division loop: from `⟨5, mem⟩` the machine reaches `⟨12, mem'⟩`
after at most `6*(m-d)+1` steps, having incremented the divisor from `d` to `m`, and every
intermediate state satisfies `VB P`. -/
theorem inner_loop_vb (P m : ℕ) (hmP : m ≤ P) :
    ∀ k, ∀ d, ∀ mem : ℕ → ℤ, m - d = k → d ≤ m → 2 ≤ d →
      mem 11 = (m : ℤ) → mem 12 = (d : ℤ) → mem 1 = 0 → mem 2 = 1 →
      (mem 13 = 0 ∨ mem 13 = 1) → mem 14 ≤ (P : ℤ) → (0 : ℤ) ≤ mem 14 →
      ∃ t ≤ 6 * (m - d) + 1, ∃ mem', run t ⟨5, mem⟩ = ⟨12, mem'⟩ ∧
        mem' 12 = (m : ℤ) ∧
        (mem' 13 = 0 ↔ (mem 13 = 0 ∨ ∃ e, d ≤ e ∧ e < m ∧ e ∣ m)) ∧
        (mem' 13 = 0 ∨ mem' 13 = 1) ∧
        (∀ i, i ≠ 12 → i ≠ 13 → i ≠ 14 → mem' i = mem i) ∧
        mem' 14 ≤ (P : ℤ) ∧ (0 : ℤ) ≤ mem' 14 ∧
        (∀ j ≤ t, ∀ pc ms, run j ⟨5, mem⟩ = ⟨pc, ms⟩ → VB P ms) := by
  intro k
  induction k with
  | zero =>
    intro d mem hk hdm hd2 hm hd h1 h2 hf h14 h14n
    have hdm' : d = m := by omega
    have hmZ : (m : ℤ) ≤ (P : ℤ) := by exact_mod_cast hmP
    have h13n : (0 : ℤ) ≤ mem 13 := by rcases hf with h | h <;> rw [h] <;> norm_num
    have h13u : mem 13 ≤ 1 := by rcases hf with h | h <;> rw [h] <;> norm_num
    have hvb : VB P mem := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hm]; linarith
      · rw [hd, hdm']; exact hmZ
      · exact h14
      · exact h14n
      · exact h13n
      · exact h13u
    have hnone : ¬ (∃ e, d ≤ e ∧ e < m ∧ e ∣ m) := by rintro ⟨e, he1, he2, _⟩; omega
    refine ⟨1, by omega, mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [run_succ, run_zero]; rw [st5eq _ (by rw [hd, hdm', hm])]
    · rw [hd, hdm']
    · simp [hnone]
    · exact hf
    · intro i _ _ _; rfl
    · exact h14
    · exact h14n
    · intro j hj pc ms hrun
      have hj1 : j = 0 ∨ j = 1 := by omega
      rcases hj1 with rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvb
      · simp only [run_succ, run_zero] at hrun
        rw [st5eq _ (by rw [hd, hdm', hm])] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvb
  | succ k ih =>
    intro d mem hk hdm hd2 hm hd h1 h2 hf h14 h14n
    have hlt : d < m := by omega
    have hmZ : (m : ℤ) ≤ (P : ℤ) := by exact_mod_cast hmP
    have hne : mem 12 ≠ mem 11 := by rw [hd, hm]; exact_mod_cast (ne_of_lt hlt)
    have hlo : mem 12 < mem 11 := by rw [hd, hm]; exact_mod_cast hlt
    have h2r : (2 : ℤ) ≤ mem 12 := by rw [hd]; exact_mod_cast hd2
    have h11m : mem 11 ≤ (P : ℤ) := by rw [hm]; exact hmZ
    have h13n : (0 : ℤ) ≤ mem 13 := by rcases hf with h | h <;> rw [h] <;> norm_num
    have h13u : mem 13 ≤ 1 := by rcases hf with h | h <;> rw [h] <;> norm_num
    obtain ⟨mem1, hrun1, h12i, h11i, h14i, h14ni, hiffi, hflagi, h1i, h2i, hfri, hboundi⟩ :=
      inner_iter_vb P mem hne h11m h2r hlo h1 h2 h14 h14n h13n h13u
    have hm1 : mem1 11 = (m : ℤ) := by rw [h11i, hm]
    have hd1 : mem1 12 = ((d + 1 : ℕ) : ℤ) := by
      rw [h12i, hd, h2, Nat.cast_add, Nat.cast_one]
    have h11_1 : mem1 1 = 0 := by rw [h1i, h1]
    have h21_1 : mem1 2 = 1 := by rw [h2i, h2]
    have hflag0d : (mem1 13 = 0 ↔ (d ∣ m ∨ mem 13 = 0)) := by
      rw [hiffi, hm, hd, propext (int_rem_zero_iff m d)]
    have hkk : m - (d + 1) = k := by omega
    obtain ⟨t', ht', mem2, hrun2, h12', hiff', hflag', hfr', h14', h14n', hbound'⟩ :=
      ih (d + 1) mem1 hkk (by omega) (by omega : 2 ≤ d + 1) hm1 hd1 h11_1 h21_1 hflagi h14i h14ni
    refine ⟨6 + t', by omega, mem2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, hrun1, hrun2]
    · exact h12'
    · rw [hiff', hflag0d, exists_div_iff m d hlt]; tauto
    · exact hflag'
    · intro i hi1 hi2 hi3; rw [hfr' i hi1 hi2 hi3, hfri i hi1 hi2 hi3]
    · exact h14'
    · exact h14n'
    · exact VB_concat P ⟨5, mem⟩ ⟨5, mem1⟩ 6 t' hrun1 hboundi hbound'


/-- One full trial-division phase for a candidate `m ≤ P`: from `⟨2, mem⟩` the machine returns
to `⟨2, mem'⟩`, and *every* intermediate state satisfies `VB P`. -/
theorem phase_vb (n P c m : ℕ) (out : ℕ → ℤ) (mem : ℕ → ℤ)
    (hc : c < n) (hm : 2 ≤ m) (hmP : m ≤ P) (hG : Good n c m out mem) (hvb : VB P mem) :
    ∃ t ≤ 6 * m + 12, ∃ mem', run t ⟨2, mem⟩ = ⟨2, mem'⟩ ∧
      Good n (if Nat.Prime m then c + 1 else c) (m + 1)
        (if Nat.Prime m then Function.update out c (m : ℤ) else out) mem' ∧
      VB P mem' ∧ (∀ j ≤ t, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB P ms) := by
  obtain ⟨h0, h1, h2, h3, h4, h10, h11, hout⟩ := hG
  obtain ⟨hvb11, hvb12, hvb14, hvb14n, hvb13n, hvb13u⟩ := hvb
  have hne : mem 10 ≠ mem 0 := by rw [h10, h0]; exact_mod_cast (ne_of_lt hc)
  have hmZ : (m : ℤ) ≤ (P : ℤ) := by exact_mod_cast hmP
  have hmp : (2 : ℤ) ≤ (P : ℤ) := by exact_mod_cast (le_trans hm hmP)
  have hE1 : run 3 ⟨2, mem⟩ = ⟨5, Function.update (Function.update mem 13 1) 12 2⟩ := by
    rw [show (3:ℕ) = 2 + 1 from rfl, run_succ, run_succ, run_succ, run_zero]
    rw [st2ne _ hne, st3, st4]
    simp [Function.update_apply, h1, h2, h3]
  have hpre : ∀ j ≤ 3, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB P ms := by
    intro j hj pc ms hrun
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj3 with rfl | rfl | rfl | rfl
    · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]
      exact ⟨hvb11, hvb12, hvb14, hvb14n, hvb13n, hvb13u⟩
    · simp only [run_succ, run_zero] at hrun; rw [st2ne _ hne] at hrun
      injection hrun with _ hms; rw [← hms]
      exact ⟨hvb11, hvb12, hvb14, hvb14n, hvb13n, hvb13u⟩
    · simp only [run_succ, run_zero] at hrun; rw [st2ne _ hne, st3] at hrun
      injection hrun with _ hms; rw [← hms]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by decide : (11:ℕ) ≠ 13), h11]; linarith
      · rw [Function.update_of_ne (by decide : (12:ℕ) ≠ 13)]; exact hvb12
      · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14
      · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14n
      · rw [Function.update_self, h2, h1]; norm_num
      · rw [Function.update_self, h2, h1]; norm_num
    · rw [hE1] at hrun
      injection hrun with _ hms; rw [← hms]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by decide : (11:ℕ) ≠ 12), Function.update_of_ne (by decide : (11:ℕ) ≠ 13), h11]; linarith
      · rw [Function.update_self]; exact hmp
      · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 12), Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14
      · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 12), Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14n
      · simp [Function.update_of_ne (by decide : (13:ℕ) ≠ 12)]
      · simp [Function.update_of_ne (by decide : (13:ℕ) ≠ 12)]
  have hmE11 : (Function.update (Function.update mem 13 1) 12 2) 11 = (m : ℤ) := by
    rw [Function.update_of_ne (by decide : (11:ℕ) ≠ 12), Function.update_of_ne (by decide : (11:ℕ) ≠ 13)]; exact h11
  have hmE12 : (Function.update (Function.update mem 13 1) 12 2) 12 = (2 : ℤ) := by
    rw [Function.update_self]
  have hmE1 : (Function.update (Function.update mem 13 1) 12 2) 1 = (0 : ℤ) := by
    rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 12), Function.update_of_ne (by decide : (1:ℕ) ≠ 13)]; exact h1
  have hmE2 : (Function.update (Function.update mem 13 1) 12 2) 2 = (1 : ℤ) := by
    rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 12), Function.update_of_ne (by decide : (2:ℕ) ≠ 13)]; exact h2
  have hmE13 : (Function.update (Function.update mem 13 1) 12 2) 13 = (1 : ℤ) := by
    rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 12), Function.update_self]
  have hmE14 : (Function.update (Function.update mem 13 1) 12 2) 14 ≤ (P : ℤ) := by
    rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 12), Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14
  have hmE14n : (0 : ℤ) ≤ (Function.update (Function.update mem 13 1) 12 2) 14 := by
    rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 12), Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hvb14n
  obtain ⟨t1, ht1, memL, hrunL, hL12, hLiff, hLflag, hfrL, hL14, hL14n, hboundL⟩ :=
    inner_loop_vb P m hmP (m - 2) 2 (Function.update (Function.update mem 13 1) 12 2) rfl hm
      (le_refl 2) hmE11 hmE12 hmE1 hmE2 (Or.inr hmE13) hmE14 hmE14n
  have hL11 : memL 11 = (m : ℤ) := by
    rw [hfrL 11 (by decide) (by decide) (by decide), hmE11]
  have hvbL : VB P memL := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hL11]; linarith
    · rw [hL12]; exact hmZ
    · exact hL14
    · exact hL14n
    · rcases hLflag with h | h <;> rw [h] <;> norm_num
    · rcases hLflag with h | h <;> rw [h] <;> norm_num
  have hG' : Good n c m out memL := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfrL 0 (by decide) (by decide) (by decide)]; exact h0
    · rw [hfrL 1 (by decide) (by decide) (by decide)]; exact h1
    · rw [hfrL 2 (by decide) (by decide) (by decide)]; exact h2
    · rw [hfrL 3 (by decide) (by decide) (by decide)]; exact h3
    · rw [hfrL 4 (by decide) (by decide) (by decide)]; exact h4
    · rw [hfrL 10 (by decide) (by decide) (by decide)]; exact h10
    · rw [hfrL 11 (by decide) (by decide) (by decide)]; exact h11
    · intro j
      rw [hfrL (BASE + j) (by rw [BASE]; omega) (by rw [BASE]; omega) (by rw [BASE]; omega),
          Function.update_of_ne (by rw [BASE]; omega : BASE + j ≠ 12),
          Function.update_of_ne (by rw [BASE]; omega : BASE + j ≠ 13)]
      exact hout j
  have hfl' : memL 13 = 0 ↔ ∃ e, 2 ≤ e ∧ e < m ∧ e ∣ m := by
    rw [hLiff, show ((Function.update (Function.update mem 13 1) 12 2) 13 = (0 : ℤ)) = False by
      rw [hmE13]; norm_num]
    simp
  have hprime : memL 13 = 1 ↔ Nat.Prime m := prime_iff_flag m hm (memL 13) hfl' hLflag
  have hpl : ∀ j ≤ 3 + t1, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB P ms :=
    VB_concat P ⟨2, mem⟩ ⟨5, Function.update (Function.update mem 13 1) 12 2⟩ 3 t1 hE1 hpre hboundL
  have hmid : run (3 + t1) ⟨2, mem⟩ = ⟨12, memL⟩ := by rw [run_add, hE1, hrunL]
  by_cases hp : Nat.Prime m
  · have h13 : memL 13 = 1 := hprime.mpr hp
    have h12c : memL 13 = memL 2 := by rw [h13, hG'.2.2.1]
    obtain ⟨memR, hrunR, hGR⟩ := exit_prime n c m out memL hG' h13
    have hexit : ∀ j ≤ 6, ∀ pc ms, run j ⟨12, memL⟩ = ⟨pc, ms⟩ → VB P ms := by
      set F1 : ℕ → ℤ := Function.update memL 15 (memL 4 + memL 10) with hF1
      set F2 : ℕ → ℤ := Function.update F1 (F1 15).toNat (F1 11) with hF2
      set F3 : ℕ → ℤ := Function.update F2 10 (F2 10 + F2 2) with hF3
      set F4 : ℕ → ℤ := Function.update F3 11 (F3 11 + F3 2) with hF4
      have hF1_15 : F1 15 = (BASE : ℤ) + (c : ℤ) := by
        rw [hF1, Function.update_self, hG'.2.2.2.2.1, hG'.2.2.2.2.2.1]
      have htn : (F1 15).toNat = BASE + c := by rw [hF1_15, ← Nat.cast_add, Int.toNat_natCast]
      have hn11 : (11 : ℕ) ≠ (F1 15).toNat := by rw [htn, BASE]; omega
      have hn12 : (12 : ℕ) ≠ (F1 15).toNat := by rw [htn, BASE]; omega
      have hn13 : (13 : ℕ) ≠ (F1 15).toNat := by rw [htn, BASE]; omega
      have hn14 : (14 : ℕ) ≠ (F1 15).toNat := by rw [htn, BASE]; omega
      have hn2 : (2 : ℕ) ≠ (F1 15).toNat := by rw [htn, BASE]; omega
      have hF2_11 : F2 11 = memL 11 := by
        rw [hF2, Function.update_of_ne hn11, hF1, Function.update_of_ne (by decide : (11:ℕ) ≠ 15)]
      have hF2_12 : F2 12 = memL 12 := by
        rw [hF2, Function.update_of_ne hn12, hF1, Function.update_of_ne (by decide : (12:ℕ) ≠ 15)]
      have hF2_13 : F2 13 = memL 13 := by
        rw [hF2, Function.update_of_ne hn13, hF1, Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]
      have hF2_14 : F2 14 = memL 14 := by
        rw [hF2, Function.update_of_ne hn14, hF1, Function.update_of_ne (by decide : (14:ℕ) ≠ 15)]
      have hF2_2 : F2 2 = memL 2 := by
        rw [hF2, Function.update_of_ne hn2, hF1, Function.update_of_ne (by decide : (2:ℕ) ≠ 15)]
      have hF3_11 : F3 11 = memL 11 := by rw [hF3, Function.update_of_ne (by decide : (11:ℕ) ≠ 10), hF2_11]
      have hF3_12 : F3 12 = memL 12 := by rw [hF3, Function.update_of_ne (by decide : (12:ℕ) ≠ 10), hF2_12]
      have hF3_13 : F3 13 = memL 13 := by rw [hF3, Function.update_of_ne (by decide : (13:ℕ) ≠ 10), hF2_13]
      have hF3_14 : F3 14 = memL 14 := by rw [hF3, Function.update_of_ne (by decide : (14:ℕ) ≠ 10), hF2_14]
      have hF3_2 : F3 2 = memL 2 := by rw [hF3, Function.update_of_ne (by decide : (2:ℕ) ≠ 10), hF2_2]
      have hF4_11 : F4 11 = (m : ℤ) + 1 := by
        rw [hF4, Function.update_self, hF3_11, hL11, hF3_2, hG'.2.2.1]
      have hF4_12 : F4 12 = memL 12 := by rw [hF4, Function.update_of_ne (by decide : (12:ℕ) ≠ 11), hF3_12]
      have hF4_13 : F4 13 = memL 13 := by rw [hF4, Function.update_of_ne (by decide : (13:ℕ) ≠ 11), hF3_13]
      have hF4_14 : F4 14 = memL 14 := by rw [hF4, Function.update_of_ne (by decide : (14:ℕ) ≠ 11), hF3_14]
      have hvbF1 : VB P F1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hF1, Function.update_of_ne (by decide : (11:ℕ) ≠ 15)]; exact hvbL.1
        · rw [hF1, Function.update_of_ne (by decide : (12:ℕ) ≠ 15)]; exact hvbL.2.1
        · rw [hF1, Function.update_of_ne (by decide : (14:ℕ) ≠ 15)]; exact hvbL.2.2.1
        · rw [hF1, Function.update_of_ne (by decide : (14:ℕ) ≠ 15)]; exact hvbL.2.2.2.1
        · rw [hF1, Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]; exact hvbL.2.2.2.2.1
        · rw [hF1, Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]; exact hvbL.2.2.2.2.2
      have hvbF2 : VB P F2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hF2_11]; exact hvbL.1
        · rw [hF2_12]; exact hvbL.2.1
        · rw [hF2_14]; exact hvbL.2.2.1
        · rw [hF2_14]; exact hvbL.2.2.2.1
        · rw [hF2_13]; exact hvbL.2.2.2.2.1
        · rw [hF2_13]; exact hvbL.2.2.2.2.2
      have hvbF3 : VB P F3 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hF3_11]; exact hvbL.1
        · rw [hF3_12]; exact hvbL.2.1
        · rw [hF3_14]; exact hvbL.2.2.1
        · rw [hF3_14]; exact hvbL.2.2.2.1
        · rw [hF3_13]; exact hvbL.2.2.2.2.1
        · rw [hF3_13]; exact hvbL.2.2.2.2.2
      have hvbF4 : VB P F4 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hF4_11]; linarith
        · rw [hF4_12]; exact hvbL.2.1
        · rw [hF4_14]; exact hvbL.2.2.1
        · rw [hF4_14]; exact hvbL.2.2.2.1
        · rw [hF4_13]; exact hvbL.2.2.2.2.1
        · rw [hF4_13]; exact hvbL.2.2.2.2.2
      intro j hj pc ms hrun
      have hj6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hj6 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbL
      · simp only [run_succ, run_zero] at hrun; rw [st12eq _ h12c] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbL
      · simp only [run_succ, run_zero] at hrun; rw [st12eq _ h12c, st14, ← hF1] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbF1
      · simp only [run_succ, run_zero] at hrun; rw [st12eq _ h12c, st14, ← hF1, st15, ← hF2] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbF2
      · simp only [run_succ, run_zero] at hrun
        rw [st12eq _ h12c, st14, ← hF1, st15, ← hF2, st16, ← hF3] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbF3
      · simp only [run_succ, run_zero] at hrun
        rw [st12eq _ h12c, st14, ← hF1, st15, ← hF2, st16, ← hF3, st17, ← hF4] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbF4
      · simp only [run_succ, run_zero] at hrun
        rw [st12eq _ h12c, st14, ← hF1, st15, ← hF2, st16, ← hF3, st17, ← hF4, st18] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbF4
    have hvbR : VB P memR := hexit 6 (le_refl 6) 2 memR hrunR
    have hboundR : ∀ j ≤ 3 + t1 + 6, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB P ms :=
      VB_concat P ⟨2, mem⟩ ⟨12, memL⟩ (3 + t1) 6
        (by rw [show (3 + t1) = 3 + t1 from rfl, hmid]) hpl hexit
    refine ⟨3 + t1 + 6, by nlinarith [ht1, Nat.sub_le m 2], memR, ?_, ?_, hvbR, hboundR⟩
    · rw [show 3 + t1 + 6 = (3 + t1) + 6 from by ring, run_add, hmid, hrunR]
    · simp only [if_pos hp]; exact hGR
  · have h12c : memL 13 ≠ memL 2 := by
      rw [hG'.2.2.1]; intro hh; exact hp (hprime.mp hh)
    obtain ⟨memR, hrunR, hGR⟩ := exit_comp n c m out memL hG' h12c
    have hexit : ∀ j ≤ 4, ∀ pc ms, run j ⟨12, memL⟩ = ⟨pc, ms⟩ → VB P ms := by
      set G1 : ℕ → ℤ := Function.update memL 11 (memL 11 + memL 2) with hG1
      have hG1_11 : G1 11 = (m : ℤ) + 1 := by rw [hG1, Function.update_self, hL11, hG'.2.2.1]
      have hG1_12 : G1 12 = memL 12 := by rw [hG1, Function.update_of_ne (by decide : (12:ℕ) ≠ 11)]
      have hG1_13 : G1 13 = memL 13 := by rw [hG1, Function.update_of_ne (by decide : (13:ℕ) ≠ 11)]
      have hG1_14 : G1 14 = memL 14 := by rw [hG1, Function.update_of_ne (by decide : (14:ℕ) ≠ 11)]
      have hvbG1 : VB P G1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hG1_11]; linarith
        · rw [hG1_12]; exact hvbL.2.1
        · rw [hG1_14]; exact hvbL.2.2.1
        · rw [hG1_14]; exact hvbL.2.2.2.1
        · rw [hG1_13]; exact hvbL.2.2.2.2.1
        · rw [hG1_13]; exact hvbL.2.2.2.2.2
      intro j hj pc ms hrun
      have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj4 with rfl | rfl | rfl | rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbL
      · simp only [run_succ, run_zero] at hrun; rw [st12ne _ h12c] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbL
      · simp only [run_succ, run_zero] at hrun; rw [st12ne _ h12c, st13] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbL
      · simp only [run_succ, run_zero] at hrun; rw [st12ne _ h12c, st13, st17, ← hG1] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbG1
      · simp only [run_succ, run_zero] at hrun; rw [st12ne _ h12c, st13, st17, ← hG1, st18] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvbG1
    have hvbR : VB P memR := hexit 4 (le_refl 4) 2 memR hrunR
    have hboundR : ∀ j ≤ 3 + t1 + 4, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB P ms :=
      VB_concat P ⟨2, mem⟩ ⟨12, memL⟩ (3 + t1) 4 (by rw [hmid]) hpl hexit
    refine ⟨3 + t1 + 4, by nlinarith [ht1, Nat.sub_le m 2], memR, ?_, ?_, hvbR, hboundR⟩
    · rw [show 3 + t1 + 4 = (3 + t1) + 4 from by ring, run_add, hmid, hrunR]
    · simp only [if_neg hp]; exact hGR

/-- Soundness of `run_upto` carried together with the amplitude invariant. -/
theorem run_upto_vb (n : ℕ) (hn : 1 ≤ n) (P : ℕ) (hP : P = Nat.nth Nat.Prime (n - 1)) :
    ∀ m, 2 ≤ m → m ≤ P + 1 →
      ∃ t ≤ 6 * m * m + 14 * m, ∃ mem : ℕ → ℤ, run t ⟨2, initMem n⟩ = ⟨2, mem⟩ ∧
        Good n (Nat.primeCounting' m) m (outInf m) mem ∧ VB P mem ∧
        (∀ j ≤ t, ∀ pc ms, run j ⟨2, initMem n⟩ = ⟨pc, ms⟩ → VB P ms) := by
  have hP2 : 2 ≤ P := by rw [hP]; have := Nat.add_two_le_nth_prime (n - 1); omega
  have hvb0 : VB P (initMem n) := by
    have e11 : (initMem n) 11 = (2 : ℤ) := by simp [initMem]
    have e12 : (initMem n) 12 = (0 : ℤ) := by simp [initMem]
    have e13 : (initMem n) 13 = (0 : ℤ) := by simp [initMem]
    have e14 : (initMem n) 14 = (0 : ℤ) := by simp [initMem]
    have hPZ : (2 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP2
    have hPZ0 : (0 : ℤ) ≤ (P : ℤ) := by exact_mod_cast (Nat.zero_le P)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e11]; linarith
    · rw [e12]; linarith
    · rw [e14]; linarith
    · simp [e14]
    · simp [e13]
    · simp [e13]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm2 hmle
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · interval_cases m
      refine ⟨0, by norm_num, initMem n, by rw [run_zero], ?_, hvb0, ?_⟩
      · have hπ : Nat.primeCounting' 2 = 0 := by decide
        rw [hπ]
        have hout0 : outInf 2 = (fun _ => 0) := by funext i; simp only [outInf, hπ]; simp
        rw [hout0]; exact Good_s0 n
      · intro j hj pc ms hrun
        have hj0 : j = 0 := by omega
        subst hj0; simp only [run_zero] at hrun
        injection hrun with _ hms; rw [← hms]; exact hvb0
    · have hprev2 : 2 ≤ m - 1 := by omega
      have hprevle : m - 1 ≤ P + 1 := by omega
      obtain ⟨t, ht, mem, hrun, hG, hvb, hbound⟩ := ih (m - 1) (by omega) hprev2 hprevle
      have hc : Nat.primeCounting' (m - 1) < n := by
        have hmono : Nat.primeCounting' (m - 1) ≤ Nat.primeCounting' (Nat.nth Nat.Prime (n - 1)) :=
          Nat.monotone_primeCounting' (by omega)
        rw [Nat.primeCounting'_nth_eq] at hmono
        omega
      have hmP : m - 1 ≤ P := by omega
      obtain ⟨t', ht', mem', hrun', hG', hvb', hbound'⟩ :=
        phase_vb n P (Nat.primeCounting' (m - 1)) (m - 1) (outInf (m - 1)) mem hc (by omega) hmP hG hvb
      have hm1 : m - 1 + 1 = m := by omega
      refine ⟨t + t', ?_, mem', ?_, ?_, ?_, ?_⟩
      · exact le_trans (add_le_add ht ht') (by nlinarith [hm1, Nat.zero_le (m - 1)])
      · rw [run_add, hrun, hrun']
      · rw [show m = m - 1 + 1 from hm1.symm]
        rw [outInf_succ (m - 1), pcs_succ (m - 1)]
        rw [show Nat.primeCounting' (m - 1) + (if Nat.Prime (m - 1) then 1 else 0)
              = (if Nat.Prime (m - 1) then Nat.primeCounting' (m - 1) + 1 else Nat.primeCounting' (m - 1)) from by
            by_cases hpc : Nat.Prime (m - 1) <;> simp [hpc]]
        exact hG'
      · exact hvb'
      · exact VB_concat P ⟨2, initMem n⟩ ⟨2, mem⟩ t t' hrun hbound hbound'

/-- Combining `main`'s output guarantee with the amplitude bound: the whole run keeps every
data register (candidate `mem 11`, divisor `mem 12`, flag `mem 13`, remainder `mem 14`)
at most `p_n + 1`. -/
theorem main_bounded (n : ℕ) :
    ∃ T ≤ 700 * (n + 1) ^ 4 + 100, ∃ mem : ℕ → ℤ,
      run T (s0 n) = ⟨19, mem⟩ ∧
      (∀ j, j < n → mem (BASE + j) = (Nat.nth Nat.Prime j : ℤ)) ∧
      (∀ t ≤ T, ∀ pc ms, run t (s0 n) = ⟨pc, ms⟩ →
        ∀ i ∈ dataRegs, ms i ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) + 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hP0 : Nat.nth Nat.Prime (0 - 1) = 2 := by
      rw [show (0 : ℕ) - 1 = 0 from rfl]; exact Nat.nth_prime_zero_eq_two
    have hvbI : VB (Nat.nth Nat.Prime (0 - 1)) (initMem 0) := by
      rw [hP0]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    have hrun3 : run 3 (s0 0) = ⟨19, initMem 0⟩ := by
      rw [show (3:ℕ) = 2 + 1 from rfl, run_succ, setup 0, st2eq _ (by simp [initMem])]
    refine ⟨3, by norm_num, initMem 0, hrun3, ?_, ?_⟩
    · intro j hj; omega
    · intro t ht pc ms hrun
      refine VB_dataRegs _ _ ?_
      have ht3 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
      rcases ht3 with rfl | rfl | rfl | rfl
      · simp only [run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbI
      · simp only [run_succ, run_zero] at hrun
        rw [show step (s0 0) = ⟨1, Function.update (initMem 0) 10 ((initMem 0) 1 + (initMem 0) 1)⟩ from by
          simp [step, prog, Op.exec, s0]] at hrun
        injection hrun with _ hms; rw [← hms]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by decide : (11:ℕ) ≠ 10)]; exact hvbI.1
        · rw [Function.update_of_ne (by decide : (12:ℕ) ≠ 10)]; exact hvbI.2.1
        · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hvbI.2.2.1
        · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hvbI.2.2.2.1
        · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hvbI.2.2.2.2.1
        · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hvbI.2.2.2.2.2
      · rw [setup 0] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbI
      · rw [hrun3] at hrun; injection hrun with _ hms; rw [← hms]; exact hvbI
  · have hM : Nat.nth Nat.Prime (n - 1) ≤ 8 * n ^ 2 := by
      have := nth_prime_le (n - 1)
      rwa [Nat.sub_add_cancel hn] at this
    have hP2 : 2 ≤ Nat.nth Nat.Prime (n - 1) := by
      have := Nat.add_two_le_nth_prime (n - 1); omega
    obtain ⟨t, ht, mem, hrun, hG, hvb, hbound⟩ :=
      run_upto_vb n hn (Nat.nth Nat.Prime (n - 1)) rfl (Nat.nth Nat.Prime (n - 1) + 1)
        (by have h := Nat.add_two_le_nth_prime (n - 1); omega) (le_refl _)
    obtain ⟨g0, g1, g2, g3, g4, g10, g11, gout⟩ := hG
    have hcount : Nat.primeCounting' (Nat.nth Nat.Prime (n - 1) + 1) = n := by
      rw [pcs_succ (Nat.nth Nat.Prime (n - 1)), Nat.primeCounting'_nth_eq (n - 1)]
      rw [if_pos (Nat.prime_nth_prime (n - 1))]; omega
    have hvbI : VB (Nat.nth Nat.Prime (n - 1)) (initMem n) := by
      have e11 : (initMem n) 11 = (2 : ℤ) := by simp [initMem]
      have e12 : (initMem n) 12 = (0 : ℤ) := by simp [initMem]
      have e13 : (initMem n) 13 = (0 : ℤ) := by simp [initMem]
      have e14 : (initMem n) 14 = (0 : ℤ) := by simp [initMem]
      have hPZ : (2 : ℤ) ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) := by exact_mod_cast hP2
      have hPZ0 : (0 : ℤ) ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) := by exact_mod_cast (Nat.zero_le _)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e11]; linarith
      · rw [e12]; linarith
      · rw [e14]; linarith
      · simp [e14]
      · simp [e13]
      · simp [e13]
    have hsetup : ∀ j ≤ 2, ∀ pc ms, run j (s0 n) = ⟨pc, ms⟩ → VB (Nat.nth Nat.Prime (n - 1)) ms := by
      intro j hj pc ms hrunj
      have hj2 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj2 with rfl | rfl | rfl
      · simp only [run_zero] at hrunj; injection hrunj with _ hms; rw [← hms]; exact hvbI
      · simp only [run_succ, run_zero] at hrunj
        rw [show step (s0 n) = ⟨1, Function.update (initMem n) 10 ((initMem n) 1 + (initMem n) 1)⟩ from by
          simp [step, prog, Op.exec, s0]] at hrunj
        injection hrunj with _ hms; rw [← hms]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by decide : (11:ℕ) ≠ 10)]; exact hvbI.1
        · rw [Function.update_of_ne (by decide : (12:ℕ) ≠ 10)]; exact hvbI.2.1
        · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hvbI.2.2.1
        · rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hvbI.2.2.2.1
        · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hvbI.2.2.2.2.1
        · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hvbI.2.2.2.2.2
      · rw [setup n] at hrunj; injection hrunj with _ hms; rw [← hms]; exact hvbI
    have hcomp1 : ∀ j ≤ 2 + t, ∀ pc ms, run j (s0 n) = ⟨pc, ms⟩ → VB (Nat.nth Nat.Prime (n - 1)) ms :=
      VB_concat (Nat.nth Nat.Prime (n - 1)) (s0 n) ⟨2, initMem n⟩ 2 t (setup n) hsetup hbound
    have hhalt : ∀ j ≤ 1, ∀ pc ms, run j ⟨2, mem⟩ = ⟨pc, ms⟩ → VB (Nat.nth Nat.Prime (n - 1)) ms := by
      intro j hj pc ms hrunj
      have hj1 : j = 0 ∨ j = 1 := by omega
      rcases hj1 with rfl | rfl
      · simp only [run_zero] at hrunj; injection hrunj with _ hms; rw [← hms]; exact hvb
      · simp only [run_succ, run_zero] at hrunj
        rw [st2eq _ (by rw [g10, hcount]; exact g0.symm)] at hrunj
        injection hrunj with _ hms; rw [← hms]; exact hvb
    have hcomp2 : ∀ j ≤ (2 + t) + 1, ∀ pc ms, run j (s0 n) = ⟨pc, ms⟩ → VB (Nat.nth Nat.Prime (n - 1)) ms :=
      VB_concat (Nat.nth Nat.Prime (n - 1)) (s0 n) ⟨2, mem⟩ (2 + t) 1
        (by rw [run_add, setup n, hrun]) hcomp1 hhalt
    refine ⟨t + 3, ?_, mem, ?_, ?_, ?_⟩
    · have hM9 : Nat.nth Nat.Prime (n - 1) + 1 ≤ 9 * n ^ 2 := by nlinarith [hM, hn]
      nlinarith [ht, hM9, hn]
    · rw [show t + 3 = (2 + t) + 1 from by omega, run_add, run_add, setup n, hrun, run_succ, run_zero]
      rw [st2eq _ (by rw [g10, hcount]; exact g0.symm)]
    · intro j hj; rw [gout j]; simp only [outInf]; rw [if_pos (by rw [hcount]; exact hj)]
    · intro t' ht' pc ms hrun'
      exact VB_dataRegs _ _ (hcomp2 t' (by omega) pc ms hrun')

/-! ### Universal amplitude bound: every register stays at most `p_n + 1001`

`main_bounded` bounds only the four *data* registers written by a trial-division pass
(`mem 11`–`mem 14`).  The machine also uses auxiliary cells: the constants `mem 0 = n`,
`mem 1 = 0`, `mem 2 = 1`, `mem 3 = 2`, `mem 4 = BASE = 1000`; the counter `mem 10` (the
number of primes found so far, at most `n`); the address scratch `mem 15 = BASE + count`;
the output cells `mem (BASE + j)` (the primes, at most `p_n`); and the never-written cells
(which stay `0`).

The predicate `VInv` below records the resulting bounds for all these cells.  `vinv_step`
shows it is preserved by every instruction, `vinv_run` lifts it to the whole run, and
`main_bounded_all` states the *universal* conclusion: throughout the run **every** register
is at most `p_n + 1001 = nth Prime (n-1) + 1001`, i.e. `p_n + O(1)`. -/

-- (the literal `1000` below is `BASE`; cf. `BASE_eq`)

def VInv (n P : ℕ) (pc : ℕ) (mem : ℕ → ℤ) : Prop :=
  (∀ i, i < 1000 → (i < 10 ∨ 15 < i) → mem i = (initMem n) i) ∧
  (0 : ℤ) ≤ mem 10 ∧
  (mem 10 ≤ (n : ℤ)) ∧
  (pc = 15 → (1000 : ℤ) ≤ mem 15) ∧
  (3 ≤ pc → pc ≤ 16 → mem 10 < (n : ℤ)) ∧
  (mem 15 ≤ (n : ℤ) + 1000) ∧
  (∀ i, 1000 ≤ i → mem i ≤ (P : ℤ) + 1)

theorem vinv_zero (n P : ℕ) : VInv n P 0 (initMem n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ _; rfl
  · simp [initMem]
  · simp [initMem]
  · intro hh; omega
  · intro h3; omega
  · have h : (initMem n) 15 = (0:ℤ) := by simp [initMem]
    rw [h]; omega
  · intro i hi
    have h0 : (initMem n) i = (0:ℤ) := by simp only [initMem]; split_ifs <;> omega
    rw [h0]; omega

theorem vinv_step (n P pc0 : ℕ) (mem0 : ℕ → ℤ) (pc : ℕ) (mem : ℕ → ℤ)
    (h0 : VInv n P pc0 mem0) (h11 : mem0 11 ≤ (P : ℤ) + 1)
    (h : step ⟨pc0, mem0⟩ = ⟨pc, mem⟩) : VInv n P pc mem := by
  obtain ⟨hU, hC1, hC2, hC3, hR, hC4, hC5⟩ := h0
  rcases Nat.lt_or_ge pc0 20 with hp | hp
  · interval_cases pc0
    · rw [st0] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 10)]; exact hU i hi hi2
      · have h1 : mem0 1 = 0 := by rw [hU 1 (by norm_num) (by omega)]; simp [initMem]
        rw [Function.update_self, h1]; norm_num
      · have h1 : mem0 1 = 0 := by rw [hU 1 (by norm_num) (by omega)]; simp [initMem]
        rw [Function.update_self, h1]; omega
      · intro hh; omega
      · intro h3 h16; omega
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 10)]; exact hC5 i hi
    · rw [st1] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 11)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact hC2
      · intro hh; omega
      · intro h3 h16; omega
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 11)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 11)]; exact hC5 i hi
    · by_cases hc : mem0 10 = mem0 0
      · rw [st2eq mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro h3 h16; omega), hC4, hC5⟩
      · rw [st2ne mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        refine ⟨hU, hC1, hC2, (by intro hh; omega), ?_, hC4, hC5⟩
        intro _ _
        have h0n : mem0 0 = (n : ℤ) := by rw [hU 0 (by norm_num) (by omega)]; simp [initMem]
        omega
    · rw [st3] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 13)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 13)]; exact hC5 i hi
    · rw [st4] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 12)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 12)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 12)]; exact hC5 i hi
    · by_cases hc : mem0 12 = mem0 11
      · rw [st5eq mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
      · rw [st5ne mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
    · rw [st6] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 14)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 14)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 14)]; exact hC5 i hi
    · by_cases hc : mem0 14 = mem0 1
      · rw [st7eq mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
      · rw [st7ne mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
    · rw [st8] at h; injection h with hpc hmem; subst hpc; subst hmem
      exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
    · rw [st9] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 13)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 13)]; exact hC5 i hi
    · rw [st10] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 12)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 12)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 12)]; exact hC5 i hi
    · rw [st11] at h; injection h with hpc hmem; subst hpc; subst hmem
      exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
    · by_cases hc : mem0 13 = mem0 2
      · rw [st12eq mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
      · rw [st12ne mem0 hc] at h; injection h with hpc hmem; subst hpc; subst hmem
        exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro _ _; exact hR (by omega) (by omega)), hC4, hC5⟩
    · rw [st13] at h; injection h with hpc hmem; subst hpc; subst hmem
      exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro h3 h16; omega), hC4, hC5⟩
    · rw [st14] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 15)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 15)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 15)]; exact hC2
      · intro _
        have h4 : mem0 4 = (1000 : ℤ) := by rw [hU 4 (by norm_num) (by omega)]; simp [initMem, BASE]
        rw [Function.update_self, h4]; linarith [hC1]
      · intro h3 h16; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 15)]; exact hR (by omega) (by omega)
      · have h4 : mem0 4 = (1000 : ℤ) := by rw [hU 4 (by norm_num) (by omega)]; simp [initMem, BASE]
        rw [Function.update_self, h4]; linarith [hC2]
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 15)]; exact hC5 i hi
    · rw [st15] at h; injection h with hpc hmem; subst hpc; subst hmem
      have hge : (1000 : ℤ) ≤ mem0 15 := hC3 rfl
      have hnn : (0 : ℤ) ≤ mem0 15 := le_trans (by norm_num) hge
      have hnat : 1000 ≤ (mem0 15).toNat := by
        have hc : ((mem0 15).toNat : ℤ) = mem0 15 := Int.toNat_of_nonneg hnn
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ (mem0 15).toNat)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by omega : (10:ℕ) ≠ (mem0 15).toNat)]; exact hC1
      · rw [Function.update_of_ne (by omega : (10:ℕ) ≠ (mem0 15).toNat)]; exact hC2
      · intro hh; omega
      · intro h3 h16; rw [Function.update_of_ne (by omega : (10:ℕ) ≠ (mem0 15).toNat)]; exact hR (by omega) (by omega)
      · rw [Function.update_of_ne (by omega : (15:ℕ) ≠ (mem0 15).toNat)]; exact hC4
      · intro i hi
        by_cases hid : i = (mem0 15).toNat
        · subst hid; rw [Function.update_self]; exact h11
        · rw [Function.update_of_ne hid]; exact hC5 i hi
    · rw [st16] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 10)]; exact hU i hi hi2
      · have h2 : mem0 2 = 1 := by rw [hU 2 (by norm_num) (by omega)]; simp [initMem]
        rw [Function.update_self]
        have h2n : (0:ℤ) ≤ mem0 2 := by rw [h2]; norm_num
        linarith [hC1, h2n]
      · have h2 : mem0 2 = 1 := by rw [hU 2 (by norm_num) (by omega)]; simp [initMem]
        rw [Function.update_self]
        have hlt : mem0 10 < (n : ℤ) := hR (by omega) (by omega)
        have h2n : (0:ℤ) ≤ mem0 2 := by rw [h2]; norm_num
        linarith [hlt, h2n]
      · intro hh; omega
      · intro h3 h16; omega
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 10)]; exact hC5 i hi
    · rw [st17] at h; injection h with hpc hmem; subst hpc; subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi hi2; rw [Function.update_of_ne (by omega : i ≠ 11)]; exact hU i hi hi2
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact hC1
      · rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact hC2
      · intro hh; omega
      · intro h3 h16; omega
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 11)]; exact hC4
      · intro i hi; rw [Function.update_of_ne (by omega : i ≠ 11)]; exact hC5 i hi
    · rw [st18] at h; injection h with hpc hmem; subst hpc; subst hmem
      exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro h3 h16; omega), hC4, hC5⟩
    · rw [st19] at h; injection h with hpc hmem; subst hpc; subst hmem
      exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro h3 h16; omega), hC4, hC5⟩
  · have hnone : prog[pc0]? = none := by
      rw [List.getElem?_eq_none_iff]; simp [prog]; omega
    simp only [step, hnone] at h
    injection h with hpc hmem; subst hpc; subst hmem
    exact ⟨hU, hC1, hC2, (by intro hh; omega), (by intro h3 h16; omega), hC4, hC5⟩

theorem vinv_run (n P : ℕ) (T : ℕ)
    (h11 : ∀ t ≤ T, ∀ pc ms, run t (s0 n) = ⟨pc, ms⟩ → ms 11 ≤ (P : ℤ) + 1) :
    ∀ t ≤ T, ∀ pc ms, run t (s0 n) = ⟨pc, ms⟩ → VInv n P pc ms := by
  intro t
  induction t with
  | zero =>
    intro _ pc ms h
    simp only [run_zero] at h
    injection h with hpc hmem; subst hpc; subst hmem
    exact vinv_zero n P
  | succ t ih =>
    intro ht pc ms h
    rw [run_succ] at h
    exact vinv_step n P _ _ pc ms (ih (by omega) _ _ rfl) (h11 t (by omega) _ _ rfl) h

lemma initMem_le (n P : ℕ) (hn : (n : ℤ) ≤ (P : ℤ) + 1001) (h2 : (2 : ℤ) ≤ (P : ℤ)) :
    ∀ i, (initMem n) i ≤ (P : ℤ) + 1001 := by
  intro i
  simp only [initMem, BASE_eq]
  split_ifs <;> omega

theorem main_bounded_all (n : ℕ) :
    ∃ T ≤ 700 * (n + 1) ^ 4 + 100, ∃ mem : ℕ → ℤ,
      run T (s0 n) = ⟨19, mem⟩ ∧
      (∀ j, j < n → mem (BASE + j) = (Nat.nth Nat.Prime j : ℤ)) ∧
      (∀ t ≤ T, ∀ pc ms, run t (s0 n) = ⟨pc, ms⟩ →
        ∀ i, ms i ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) + 1001) := by
  obtain ⟨T, hT, mem, hrun, hout, hdata⟩ := main_bounded n
  refine ⟨T, hT, mem, hrun, hout, ?_⟩
  intro t ht pc ms hrun' i
  have hPn : (n : ℤ) ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) := by
    have := Nat.add_two_le_nth_prime (n - 1); omega
  have hP2 : (2 : ℤ) ≤ (Nat.nth Nat.Prime (n - 1) : ℤ) := by
    have := Nat.add_two_le_nth_prime (n - 1); omega
  have hv := vinv_run n (Nat.nth Nat.Prime (n - 1)) T
      (fun j hj pc ms h => hdata j hj pc ms h 11 (by decide)) t ht pc ms hrun'
  obtain ⟨hU, hC1, hC2, hC3, hR, hC4, hC5⟩ := hv
  rcases lt_or_ge i 1000 with hi | hi
  · rcases lt_or_ge i 10 with hi10 | hi10
    · rw [hU i hi (Or.inl hi10)]
      exact initMem_le n (Nat.nth Nat.Prime (n - 1)) (by omega) hP2 i
    · rcases lt_or_ge 15 i with hi15 | hi15
      · rw [hU i hi (Or.inr hi15)]
        exact initMem_le n (Nat.nth Nat.Prime (n - 1)) (by omega) hP2 i
      · interval_cases i
        · exact le_trans hC2 (by omega)
        · exact le_trans (hdata t ht pc ms hrun' 11 (by decide)) (by omega)
        · exact le_trans (hdata t ht pc ms hrun' 12 (by decide)) (by omega)
        · exact le_trans (hdata t ht pc ms hrun' 13 (by decide)) (by omega)
        · exact le_trans (hdata t ht pc ms hrun' 14 (by decide)) (by omega)
        · exact le_trans hC4 (by omega)
  · exact le_trans (hC5 i hi) (by omega)

end BkSet.RAM


end


-- ===============================================================================================
-- ==  Section `RamLog` proving that the discrete logarithm in the smooth cyclic group is in P  ==
-- ===============================================================================================

section

/-
# Discrete logarithm modulo `2^r` 

This file formalises the `O(r^2)` discrete-logarithm algorithm of Lemma 1 of the attached
paper, on the RAM model from `PrimeGen` section (the instruction set `Op`, machine
state `State` and step function `Op.exec` are reused verbatim; only the program differs).

Input convention: `mem 0 = r`, `mem 1 = p` (an odd integer, `1 <= p <= 2^r - 1`).
Output: `mem 24` holds `ind_5 p` if `p` lies in the subgroup generated by `5`, else `-1`.

Register map: `0,1` inputs; `2..7` constants `0,1,2,3,4,5`; `8` modulus `2^r`; `9` the
order-two element `2^(r-1)+1`; `10` the inverse `5^(-1) mod 2^r`; `13` loop countdown;
`14` running `q = s^(partial log)`; `15` partial log; `16` running `t = s^(2^i)`; `17`
running `2^i`; `18` product `q*p`; `19` its `2^e`-th power; `20` remaining squarings;
`21` squaring counter; `22` scratch; `24` result.

## Main results

* `BkSet.RAM.lemma1` : the concrete program `Lprog` halts within `40*(r+1)^2 + 100` steps on
  every odd `p` with `1 <= p < 2^r`.  It writes `ind_5 p` to `mem 24` and stops at `pc = 47`
  when `p` lies in the subgroup generated by `5`, and writes `-1`, stopping at `pc = 48`,
  otherwise.  This is the correctness and the `O(r^2)` step bound of Lemma 1 of the paper.
* `BkSet.RAM.lemma1_amp` : the *amplitude-equipped* form of Lemma 1.  It states the above
  together with the amplitude bound of the paper: throughout the whole run **every** register
  lies in `[-1, 2^(2r)]` (in particular `2^(2r) + O(1)`).
* Infrastructure: the prelude `prelude_run`, the loop invariant `LoopInv` with its step
  lemmas `loop_step` / `loop_fail`, the assembled loops `loop_pos` / `loop_neg`, the inner
  squaring loop `sq_loop`, and the arithmetic core `iter_core`.  The discrete-logarithm
  identities rest on `five_pow_ord2` and `main_pow2`, with the `+- 5^h` decomposition of an
  odd `p` obtained from `BkSet.reprMap_bijective`.

### The amplitude invariant

The amplitude bound is proved with a separate one-step invariant, in the style of `VB` /
`VInv` in `PrimeGen`, rather than by threading it through the correctness proof:

* `AInv r pc mem` (`structure`) bounds every register by `2^(2r)`, asserts
  non-negativity (except `mem 24 = -1`), pins the constant cells, and records the
  *pc-dependent* facts that make each instruction's result fit.  The only delicate part is
  that `mem 8` (doubling `1, 2, ..., 2^r`) and `mem 17`/`mem 15` (the running `2^i` and the
  accumulated logarithm) grow multiplicatively; `AInv` therefore ties them to their loop
  counters `mem 22` and `mem 13` (`dbl`, `bit`) and to each other (`a1`, `a2`).
* `ainv_init` : the invariant holds in the initial state.
* `ainv_step` : `AInv` is preserved by every one of the 49 instructions (49-case analysis).
* `ainv_run` : hence `AInv` holds at every time step.
-/


namespace BkSet.RAM

open Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-! ## The program -/

/-- The discrete-logarithm program.  See the module docstring for the register map. -/
def Lprog : List Op :=
  [ Op.add 8 3 2, Op.add 22 0 2, Op.jeq 22 2 6, Op.add 8 8 8, Op.sub 22 22 3, Op.jmp 2,
    Op.quo 9 8 4, Op.add 9 9 3, Op.add 10 3 2, Op.sub 22 0 4, Op.jeq 22 2 17, Op.mul 10 10 10,
    Op.rem 10 10 8, Op.mul 10 10 7, Op.rem 10 10 8, Op.sub 22 22 3, Op.jmp 10, Op.add 16 10 2,
    Op.sub 13 0 4, Op.jmp 20, Op.jgt 13 2 22, Op.jmp 46, Op.mul 18 14 1, Op.rem 18 18 8,
    Op.sub 20 13 3, Op.add 19 18 2, Op.add 21 2 2, Op.jgt 20 21 29, Op.jmp 33, Op.mul 19 19 19,
    Op.rem 19 19 8, Op.add 21 21 3, Op.jmp 27, Op.jeq 19 3 40, Op.jeq 19 9 36, Op.jmp 48,
    Op.add 15 15 17, Op.mul 14 14 16, Op.rem 14 14 8, Op.jmp 41, Op.jmp 41, Op.mul 16 16 16,
    Op.rem 16 16 8, Op.add 17 17 17, Op.sub 13 13 3, Op.jmp 20, Op.add 24 15 2, Op.halt ,
    Op.halt  ]


def Lstep (s : State) : State :=
  match Lprog[s.pc]? with
  | some op => op.exec s
  | none => s

def Lrun : ℕ → State → State
  | 0, s => s
  | (k+1), s => Lstep (Lrun k s)

@[simp] theorem Lrun_zero (s : State) : Lrun 0 s = s := rfl
@[simp] theorem Lrun_succ (k : ℕ) (s : State) : Lrun (k+1) s = Lstep (Lrun k s) := rfl

theorem Lrun_add (a b : ℕ) (s : State) : Lrun (a+b) s = Lrun b (Lrun a s) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, Lrun_succ, Lrun_succ, ih]

theorem Lst0 (mem) : Lstep ⟨0, mem⟩ = ⟨1, Function.update mem 8 (mem 3 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst1 (mem) : Lstep ⟨1, mem⟩ = ⟨2, Function.update mem 22 (mem 0 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst2eq (mem) (h : mem 22 = mem 2) : Lstep ⟨2, mem⟩ = ⟨6, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst2ne (mem) (h : mem 22 ≠ mem 2) : Lstep ⟨2, mem⟩ = ⟨3, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst3 (mem) : Lstep ⟨3, mem⟩ = ⟨4, Function.update mem 8 (mem 8 + mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst4 (mem) : Lstep ⟨4, mem⟩ = ⟨5, Function.update mem 22 (mem 22 - mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst5 (mem) : Lstep ⟨5, mem⟩ = ⟨2, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst6 (mem) : Lstep ⟨6, mem⟩ = ⟨7, Function.update mem 9 (mem 8 / mem 4)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst7 (mem) : Lstep ⟨7, mem⟩ = ⟨8, Function.update mem 9 (mem 9 + mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst8 (mem) : Lstep ⟨8, mem⟩ = ⟨9, Function.update mem 10 (mem 3 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst9 (mem) : Lstep ⟨9, mem⟩ = ⟨10, Function.update mem 22 (mem 0 - mem 4)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst10eq (mem) (h : mem 22 = mem 2) : Lstep ⟨10, mem⟩ = ⟨17, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst10ne (mem) (h : mem 22 ≠ mem 2) : Lstep ⟨10, mem⟩ = ⟨11, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst11 (mem) : Lstep ⟨11, mem⟩ = ⟨12, Function.update mem 10 (mem 10 * mem 10)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst12 (mem) : Lstep ⟨12, mem⟩ = ⟨13, Function.update mem 10 (mem 10 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst13 (mem) : Lstep ⟨13, mem⟩ = ⟨14, Function.update mem 10 (mem 10 * mem 7)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst14 (mem) : Lstep ⟨14, mem⟩ = ⟨15, Function.update mem 10 (mem 10 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst15 (mem) : Lstep ⟨15, mem⟩ = ⟨16, Function.update mem 22 (mem 22 - mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst16 (mem) : Lstep ⟨16, mem⟩ = ⟨10, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst17 (mem) : Lstep ⟨17, mem⟩ = ⟨18, Function.update mem 16 (mem 10 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst18 (mem) : Lstep ⟨18, mem⟩ = ⟨19, Function.update mem 13 (mem 0 - mem 4)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst19 (mem) : Lstep ⟨19, mem⟩ = ⟨20, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst20gt (mem) (h : mem 13 > mem 2) : Lstep ⟨20, mem⟩ = ⟨22, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst20le (mem) (h : ¬ (mem 13 > mem 2)) : Lstep ⟨20, mem⟩ = ⟨21, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst21 (mem) : Lstep ⟨21, mem⟩ = ⟨46, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst22 (mem) : Lstep ⟨22, mem⟩ = ⟨23, Function.update mem 18 (mem 14 * mem 1)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst23 (mem) : Lstep ⟨23, mem⟩ = ⟨24, Function.update mem 18 (mem 18 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst24 (mem) : Lstep ⟨24, mem⟩ = ⟨25, Function.update mem 20 (mem 13 - mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst25 (mem) : Lstep ⟨25, mem⟩ = ⟨26, Function.update mem 19 (mem 18 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst26 (mem) : Lstep ⟨26, mem⟩ = ⟨27, Function.update mem 21 (mem 2 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst27gt (mem) (h : mem 20 > mem 21) : Lstep ⟨27, mem⟩ = ⟨29, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst27le (mem) (h : ¬ (mem 20 > mem 21)) : Lstep ⟨27, mem⟩ = ⟨28, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst28 (mem) : Lstep ⟨28, mem⟩ = ⟨33, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst29 (mem) : Lstep ⟨29, mem⟩ = ⟨30, Function.update mem 19 (mem 19 * mem 19)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst30 (mem) : Lstep ⟨30, mem⟩ = ⟨31, Function.update mem 19 (mem 19 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst31 (mem) : Lstep ⟨31, mem⟩ = ⟨32, Function.update mem 21 (mem 21 + mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst32 (mem) : Lstep ⟨32, mem⟩ = ⟨27, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst33eq (mem) (h : mem 19 = mem 3) : Lstep ⟨33, mem⟩ = ⟨40, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst33ne (mem) (h : mem 19 ≠ mem 3) : Lstep ⟨33, mem⟩ = ⟨34, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst34eq (mem) (h : mem 19 = mem 9) : Lstep ⟨34, mem⟩ = ⟨36, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst34ne (mem) (h : mem 19 ≠ mem 9) : Lstep ⟨34, mem⟩ = ⟨35, mem⟩ := by simp [Lstep, Lprog, Op.exec, h]
theorem Lst35 (mem) : Lstep ⟨35, mem⟩ = ⟨48, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst36 (mem) : Lstep ⟨36, mem⟩ = ⟨37, Function.update mem 15 (mem 15 + mem 17)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst37 (mem) : Lstep ⟨37, mem⟩ = ⟨38, Function.update mem 14 (mem 14 * mem 16)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst38 (mem) : Lstep ⟨38, mem⟩ = ⟨39, Function.update mem 14 (mem 14 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst39 (mem) : Lstep ⟨39, mem⟩ = ⟨41, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst40 (mem) : Lstep ⟨40, mem⟩ = ⟨41, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst41 (mem) : Lstep ⟨41, mem⟩ = ⟨42, Function.update mem 16 (mem 16 * mem 16)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst42 (mem) : Lstep ⟨42, mem⟩ = ⟨43, Function.update mem 16 (mem 16 % mem 8)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst43 (mem) : Lstep ⟨43, mem⟩ = ⟨44, Function.update mem 17 (mem 17 + mem 17)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst44 (mem) : Lstep ⟨44, mem⟩ = ⟨45, Function.update mem 13 (mem 13 - mem 3)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst45 (mem) : Lstep ⟨45, mem⟩ = ⟨20, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst46 (mem) : Lstep ⟨46, mem⟩ = ⟨47, Function.update mem 24 (mem 15 + mem 2)⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst47 (mem) : Lstep ⟨47, mem⟩ = ⟨47, mem⟩ := by simp [Lstep, Lprog, Op.exec]
theorem Lst48 (mem) : Lstep ⟨48, mem⟩ = ⟨48, mem⟩ := by simp [Lstep, Lprog, Op.exec]

/-! ## Initial state -/

def LinitMem (r p : ℕ) : ℕ → ℤ :=
  fun i => if i = 0 then (r : ℤ) else if i = 1 then (p : ℤ) else if i = 2 then 0
    else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else if i = 6 then 4
    else if i = 7 then 5 else if i = 14 then 1 else if i = 17 then 1 else if i = 24 then -1
    else 0

def Ls0 (r p : ℕ) : State := ⟨0, LinitMem r p⟩

/-! ## Number-theoretic core -/

theorem two_pow_pos (k : ℕ) : 0 < 2^k := by positivity
theorem two_le_two_pow {r : ℕ} (hr : 1 ≤ r) : 2 ≤ 2^r := by
  have h : 2^r = 2^1 * 2^(r-1) := by rw [← pow_add]; congr 1; omega
  rw [h, pow_one]; exact Nat.le_mul_of_pos_right _ (two_pow_pos _)
theorem one_lt_two_pow {r : ℕ} (hr : 1 ≤ r) : 1 < 2^r := lt_of_lt_of_le (by norm_num) (two_le_two_pow hr)
theorem four_le_two_pow {r : ℕ} (hr : 3 ≤ r) : 4 ≤ 2^(r-1) := by
  have h : (2:ℕ)^(r-1) = 2^2 * 2^(r-3) := by rw [← pow_add]; congr 1; omega
  rw [h, show (2:ℕ)^2 = 4 by norm_num]; exact Nat.le_mul_of_pos_right _ (two_pow_pos _)
theorem two_le_two_pow_pred {r : ℕ} (hr : 2 ≤ r) : 2 ≤ 2^(r-1) := by
  have h : (2:ℕ)^(r-1) = 2^1 * 2^(r-2) := by rw [← pow_add]; congr 1; omega
  rw [h, pow_one]; exact Nat.le_mul_of_pos_right _ (two_pow_pos _)
theorem two_mul_pow_pred (r : ℕ) (hr : 1 ≤ r) : (2:ℕ) * 2^(r-1) = 2^r := by
  conv_rhs => rw [show r = (r-1)+1 by omega, Nat.pow_succ]
  ring
theorem mul_two_pow_pred (r : ℕ) (hr : 1 ≤ r) : (2:ℕ)^(r-1) * 2 = 2^r := by
  conv_rhs => rw [show r = (r-1)+1 by omega, Nat.pow_succ]
theorem two_mul_pow_pred_int (r : ℕ) (hr : 1 ≤ r) : (2:ℤ)^(r-1) * 2 = (2:ℤ)^r := by
  conv_rhs => rw [show r = (r-1)+1 by omega, pow_succ]

-- tests for coercion forms
example (r : ℕ) : (5 : ZMod (2^r))^(2^(r-3)) = (((5^(2^(r-3)) : ℕ)) : ZMod (2^r)) := by
  rw [Nat.cast_pow]; norm_num
example (r : ℕ) : ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) = (((1 + 2^(r-1) : ℤ)) : ZMod (2^r)) := by
  push_cast; ring

theorem five_pow_ord2 (r : ℕ) (hr : 3 ≤ r) :
    (5 : ZMod (2^r))^(2^(r-3)) = ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) := by
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ)
    (p := 2) (u := (4 : ℤ)) (v := (2 : ℤ)) Nat.prime_two
    ⟨2, by norm_num⟩ ⟨1, by norm_num⟩ (1 : ℤ) (r - 3)
  have h5 : ((1 : ℤ) + 4 * 1)^(2^(r-3)) = (5 : ℤ)^(2^(r-3)) := by norm_num
  rw [h5] at hy
  push_cast at hy
  have hz : (2 : ℤ)^(r-3) * 4 = (2 : ℤ)^(r-1) := by
    rw [show (4 : ℤ) = (2 : ℤ)^2 by norm_num, ← pow_add]; congr 1; omega
  rw [hz] at hy
  have hy' : (5 : ℤ)^(2^(r-3)) = (1 + 2^(r-1) : ℤ) + (2:ℤ)^r * y := by
    rw [hy]
    rw [show (2:ℤ)^(r-1) * (1 + 2*y) = (2:ℤ)^(r-1) + (2:ℤ)^r * y by
          rw [mul_add, mul_one, show (2:ℤ)^(r-1) * (2*y) = (2:ℤ)^r * y by
                rw [← mul_assoc, two_mul_pow_pred_int r (by omega)]]]
    ring
  have hnat : (5^(2^(r-3))) ≡ (1 + 2^(r-1)) [MOD 2^r] := by
    rw [Nat.modEq_iff_dvd]
    have hdiff : (((1 + 2^(r-1) : ℕ)) : ℤ) - (((5^(2^(r-3)) : ℕ)) : ℤ) = -((2:ℤ)^r * y) := by
      push_cast; rw [hy']; ring
    rw [hdiff, show (((2:ℕ)^r : ℕ) : ℤ) = (2:ℤ)^r by push_cast; ring]
    exact dvd_neg.mpr (dvd_mul_right ((2:ℤ)^r) y)
  rw [show (5 : ZMod (2^r))^(2^(r-3)) = (((5^(2^(r-3)) : ℕ)) : ZMod (2^r)) by
        rw [Nat.cast_pow]; norm_num, ZMod.natCast_eq_natCast_iff']
  exact hnat

theorem two_ne_zero (r : ℕ) (hr : 2 ≤ r) : (2 : ZMod (2^r)) ≠ 0 := by
  intro h
  rw [show (2 : ZMod (2^r)) = ((2 : ℕ) : ZMod (2^r)) by norm_num, ZMod.natCast_eq_zero_iff] at h
  have h' : 2^r ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have hlt : 2^1 < 2^r := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 1 < r)
  omega

theorem four_ne_zero (r : ℕ) (hr : 3 ≤ r) : (4 : ZMod (2^r)) ≠ 0 := by
  intro h
  rw [show (4 : ZMod (2^r)) = ((4 : ℕ) : ZMod (2^r)) by norm_num, ZMod.natCast_eq_zero_iff] at h
  have h' : 2^r ≤ 4 := Nat.le_of_dvd (by norm_num) h
  have hlt : 2^2 < 2^r := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 2 < r)
  omega

theorem h_two (r : ℕ) (hr : 1 ≤ r) :
    (2 : ZMod (2^r)) * ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) = 2 := by
  have hl : (2 : ZMod (2^r)) * ((1 + 2^(r-1) : ℕ) : ZMod (2^r))
      = ((2 * (1 + 2^(r-1)) : ℕ) : ZMod (2^r)) := by push_cast; ring
  rw [hl, show (2 : ZMod (2^r)) = ((2 : ℕ) : ZMod (2^r)) by norm_num,
      ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
  have hkey : (2 * (1 + 2^(r-1)) : ℕ) = 2 + 2^r := by
    rw [mul_add, mul_one, mul_comm 2 (2^(r-1)), mul_two_pow_pred r hr]
  rw [hkey]
  have he : (((2 : ℕ)) : ℤ) - ((2 + 2^r : ℕ) : ℤ) = -(((2 : ℕ)^r : ℤ)) := by push_cast; ring
  rw [he]
  exact dvd_neg.mpr (dvd_refl _)

theorem lt_two_pow (r : ℕ) (hr : 2 ≤ r) : 1 + 2^(r-1) < 2^r := by
  rw [← mul_two_pow_pred r (by omega : 1 ≤ r)]
  have := two_le_two_pow_pred hr
  omega

theorem h_ne_one (r : ℕ) (hr : 2 ≤ r) : ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) ≠ 1 := by
  intro h
  rw [show (1 : ZMod (2^r)) = ((1 : ℕ) : ZMod (2^r)) by norm_num,
      ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (lt_two_pow r hr),
      Nat.mod_eq_of_lt (one_lt_two_pow (by omega : 1 ≤ r))] at h
  have hp : 0 < (2:ℕ)^(r-1) := two_pow_pos _
  omega

theorem h_ne_negone (r : ℕ) (hr : 3 ≤ r) : ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) ≠ -1 := by
  intro h
  have hneg : (-1 : ZMod (2^r)) = ((2^r - 1 : ℕ) : ZMod (2^r)) := by
    have h1 : ((2^r - 1 : ℕ) : ZMod (2^r)) = ((2^r : ℕ) : ZMod (2^r)) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
    rw [h1, ZMod.natCast_self]; ring
  rw [hneg, ZMod.natCast_eq_natCast_iff'] at h
  have e1 : (1 + 2^(r-1)) % 2^r = 1 + 2^(r-1) := Nat.mod_eq_of_lt (lt_two_pow r (by omega))
  have e2 : (2^r - 1) % 2^r = 2^r - 1 := Nat.mod_eq_of_lt (Nat.sub_lt (two_pow_pos r) (by norm_num))
  rw [e1, e2] at h
  have h3 : (2:ℕ)^(r-1) * 2 = 2^r := mul_two_pow_pred r (by omega)
  have h5 : (2:ℕ)^(r-1) = 2 := by omega
  have h4 := four_le_two_pow hr
  omega

theorem neg_h_ne_h (r : ℕ) (hr : 2 ≤ r) :
    -(((1 + 2^(r-1) : ℕ) : ZMod (2^r))) ≠ ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) := by
  intro h
  have hh := h_two r (by omega)
  have key : ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) + ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) = 0 :=
    (neg_eq_iff_add_eq_zero).mp h
  have h2 : (2 : ZMod (2^r)) * (((1 + 2^(r-1) : ℕ) : ZMod (2^r))) = 0 := by
    have step : (2 : ZMod (2^r)) * (((1 + 2^(r-1) : ℕ) : ZMod (2^r)))
        = ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) + ((1 + 2^(r-1) : ℕ) : ZMod (2^r)) := by ring
    rw [step]; exact key
  rw [hh] at h2
  exact two_ne_zero r hr h2

theorem hsq (r : ℕ) (hr : 2 ≤ r) : (((1 + 2^(r-1) : ℕ) : ZMod (2^r)))^2 = 1 := by
  have hl : (((1 + 2^(r-1) : ℕ) : ZMod (2^r)))^2 = (((1 + 2^(r-1))^2 : ℕ) : ZMod (2^r)) := by
    push_cast; ring
  rw [hl, show (1 : ZMod (2^r)) = ((1 : ℕ) : ZMod (2^r)) by norm_num,
      ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
  have hkey : (1 + 2^(r-1))^2 = 1 + 2^r * (1 + 2^(r-2)) := by
    have ha : (2:ℕ)^(2*r-2) = 2^r * 2^(r-2) := by rw [← pow_add]; congr 1; omega
    have hb : 2 * 2^(r-1) = 2^r := two_mul_pow_pred r (by omega)
    have hc : (1 + 2^(r-1))^2 = 1 + 2 * 2^(r-1) + 2^(r-1) * 2^(r-1) := by ring
    rw [hc, hb, show (2:ℕ)^(r-1) * 2^(r-1) = 2^(2*r-2) by rw [← pow_add]; congr 1; omega, ha]
    ring
  rw [hkey]
  have he : (((1 : ℕ)) : ℤ) - ((1 + 2^r * (1 + 2^(r-2)) : ℕ) : ℤ)
      = -(((2^r : ℕ) : ℤ) * ((1 + 2^(r-2) : ℕ) : ℤ)) := by push_cast; ring
  rw [he]
  exact dvd_neg.mpr (dvd_mul_right ((2^r : ℕ) : ℤ) ((1 + 2^(r-2) : ℕ) : ℤ))

theorem bit_step (r : ℕ) (hr : 3 ≤ r) (a i : ℕ) (hi : i ≤ r-3) :
    ((5 : ZMod (2^r))^(a - a % 2^i))^(2^(r-3-i))
      = ((5 : ZMod (2^r))^(2^(r-3)))^((a / 2^i) % 2) := by
  have hA : a - a % 2^i = a / 2^i * 2^i := by
    have h2 : a / 2^i * 2^i + a % 2^i = a := by rw [mul_comm (a/2^i) (2^i)]; exact Nat.div_add_mod a (2^i)
    nth_rewrite 1 [← h2]
    exact Nat.add_sub_cancel _ _
  have hh2 : ((5 : ZMod (2^r))^(2^(r-3)))^2 = 1 := by
    rw [five_pow_ord2 r hr]; exact hsq r (by omega)
  have hfin : ∀ m : ℕ, ((5 : ZMod (2^r))^(2^(r-3)))^m = ((5 : ZMod (2^r))^(2^(r-3)))^(m % 2) := by
    intro m
    have hm : m = m / 2 * 2 + m % 2 := by have := Nat.div_add_mod m 2; omega
    conv_lhs => rw [hm]
    rw [pow_add, show ((5 : ZMod (2^r))^(2^(r-3)))^(m/2*2)
          = (((5 : ZMod (2^r))^(2^(r-3)))^2)^(m/2) by rw [mul_comm (m/2) 2, pow_mul],
        hh2, one_pow, one_mul]
  calc ((5 : ZMod (2^r))^(a - a % 2^i))^(2^(r-3-i))
      = (5 : ZMod (2^r))^((a / 2^i * 2^i) * 2^(r-3-i)) := by rw [hA, ← pow_mul]
    _ = (5 : ZMod (2^r))^(a / 2^i * 2^(r-3)) := by
          rw [mul_assoc, ← pow_add, show i + (r-3-i) = r-3 by omega]
    _ = ((5 : ZMod (2^r))^(2^(r-3)))^(a / 2^i) := by rw [mul_comm, pow_mul]
    _ = ((5 : ZMod (2^r))^(2^(r-3)))^((a / 2^i) % 2) := hfin _

theorem main_pow (r : ℕ) (hr : 2 ≤ r) (s : ZMod (2^r)) (hs : (5 : ZMod (2^r)) * s = 1)
    (a A j : ℕ) (hAa : A ≤ a) :
    ((-1)^j * (5 : ZMod (2^r))^a) * s^A = (-1)^j * (5 : ZMod (2^r))^(a - A) := by
  have h5 : (5 : ZMod (2^r))^a = (5 : ZMod (2^r))^(a-A) * (5 : ZMod (2^r))^A := by
    rw [← pow_add, Nat.sub_add_cancel hAa]
  have hsA : (5 : ZMod (2^r))^A * s^A = 1 := by rw [← mul_pow, hs, one_pow]
  calc ((-1)^j * (5 : ZMod (2^r))^a) * s^A
      = (-1)^j * ((5 : ZMod (2^r))^a * s^A) := by ring
    _ = (-1)^j * ((5 : ZMod (2^r))^(a-A) * ((5 : ZMod (2^r))^A * s^A)) := by rw [h5]; ring
    _ = (-1)^j * (5 : ZMod (2^r))^(a-A) := by rw [hsA, mul_one]

theorem main_pow2 (r : ℕ) (hr : 3 ≤ r) (s : ZMod (2^r)) (hs : (5 : ZMod (2^r)) * s = 1)
    (a j i : ℕ) (hi : i ≤ r-3) :
    (((-1)^j * (5 : ZMod (2^r))^a) * s^(a % 2^i))^(2^(r-3-i))
      = (-1)^(j * 2^(r-3-i)) * ((5 : ZMod (2^r))^(2^(r-3)))^((a/2^i)%2) := by
  rw [main_pow r (by omega) s hs a (a % 2^i) j (Nat.mod_le _ _), mul_pow, bit_step r hr a i hi]
  congr 1
  rw [pow_mul]



/-! ## Number-theoretic helpers for the inverse -/

theorem intCast_emod (r : ℕ) (a : ℤ) :
    (((a % (((2:ℕ)^r : ℕ) : ℤ)) : ℤ) : ZMod (2^r)) = ((a : ℤ) : ZMod (2^r)) := by
  rw [ZMod.intCast_eq_intCast_iff']
  have hpos : (0:ℤ) < (((2:ℕ)^r : ℕ) : ℤ) := by positivity
  exact Int.emod_eq_of_lt (Int.emod_nonneg _ (ne_of_gt hpos)) (Int.emod_lt_of_pos _ hpos)

theorem five_pow_orderOf (r : ℕ) (hr : 2 ≤ r) : (5 : ZMod (2^r))^(2^(r-2)) = 1 := by
  have h := ZMod.orderOf_five (r-2)
  rw [show r-2+2 = r by omega] at h
  rw [← h, pow_orderOf_eq_one]

theorem five_inv (r : ℕ) (hr : 2 ≤ r) : (5 : ZMod (2^r))^(2^(r-2)-1) * 5 = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  exact five_pow_orderOf r hr

/-! ## The doubling loop (`M := 2^r`) -/

theorem pre_double (c : ℕ) :
    ∀ (mem : ℕ → ℤ), mem 22 = (c : ℤ) → mem 2 = 0 → mem 3 = 1 →
      ∃ t ≤ 4*c + 2, ∃ mem', Lrun t ⟨2, mem⟩ = ⟨6, mem'⟩ ∧ mem' 8 = mem 8 * (2:ℤ)^c ∧
        mem' 22 = 0 ∧ (∀ i, i ≠ 8 → i ≠ 22 → mem' i = mem i) := by
  induction c with
  | zero =>
    intro mem h22 h2 h3
    refine ⟨1, by omega, mem, ?_, ?_, ?_, ?_⟩
    · simp only [Lrun_succ, Lrun_zero]; rw [Lst2eq _ (by simp [h22, h2])]
    · rw [pow_zero, mul_one]
    · exact h22
    · intro i _ _; rfl
  | succ c ih =>
    intro mem h22 h2 h3
    have hne : mem 22 ≠ mem 2 := by rw [h22, h2]; exact_mod_cast Nat.succ_ne_zero c
    set memA : ℕ → ℤ := Function.update mem 8 (mem 8 + mem 8) with hA
    set memB : ℕ → ℤ := Function.update memA 22 (memA 22 - memA 3) with hB
    have hA22 : memA 22 = mem 22 := by rw [hA, Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]
    have hA3 : memA 3 = mem 3 := by rw [hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 8)]
    have hB2 : memB 2 = 0 := by
      rw [hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 22), hA,
          Function.update_of_ne (by decide : (2:ℕ) ≠ 8)]; exact h2
    have hB3 : memB 3 = 1 := by
      rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 22), hA,
          Function.update_of_ne (by decide : (3:ℕ) ≠ 8)]; exact h3
    have hB8 : memB 8 = mem 8 + mem 8 := by
      rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 22), hA, Function.update_self]
    have hB22 : memB 22 = (c : ℤ) := by
      rw [hB, Function.update_self, hA22, hA3, h22, h3]; push_cast; ring
    obtain ⟨t, ht, memC, hrun, hC8, hC22, hCfr⟩ := ih memB hB22 hB2 hB3
    refine ⟨4 + t, by omega, memC, ?_, ?_, ?_, ?_⟩
    · rw [Lrun_add]
      rw [show Lrun 4 ⟨2, mem⟩ = ⟨2, memB⟩ from by
            rw [show (4:ℕ) = 3+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
            rw [Lst2ne mem hne, Lst3, ← hA, Lst4, ← hB, Lst5]]
      exact hrun
    · rw [hC8, hB8, show (2:ℤ)^(c+1) = (2:ℤ)^c * 2 by rw [pow_succ]]; ring
    · exact hC22
    · intro i hi1 hi2
      rw [hCfr i hi1 hi2, hB, Function.update_of_ne (by omega : i ≠ 22), hA,
          Function.update_of_ne (by omega : i ≠ 8)]

/-! ## The inverse loop body -/

theorem s_body (mem : ℕ → ℤ) :
    ∃ mem', Lrun 6 ⟨11, mem⟩ = ⟨10, mem'⟩ ∧
      mem' 10 = ((mem 10 * mem 10) % mem 8 * mem 7) % mem 8 ∧
      mem' 22 = mem 22 - mem 3 ∧
      (∀ i, i ≠ 10 → i ≠ 22 → mem' i = mem i) := by
  set memA : ℕ → ℤ := Function.update mem 10 (mem 10 * mem 10) with hA
  set memB : ℕ → ℤ := Function.update memA 10 (memA 10 % memA 8) with hB
  set memC : ℕ → ℤ := Function.update memB 10 (memB 10 * memB 7) with hC
  set memD : ℕ → ℤ := Function.update memC 10 (memC 10 % memC 8) with hD
  set memE : ℕ → ℤ := Function.update memD 22 (memD 22 - memD 3) with hE
  have hA8 : memA 8 = mem 8 := by rw [hA, Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]
  have hA7 : memA 7 = mem 7 := by rw [hA, Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]
  have hA10 : memA 10 = mem 10 * mem 10 := by rw [hA, Function.update_self]
  have hB8 : memB 8 = mem 8 := by rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 10), hA8]
  have hB7 : memB 7 = mem 7 := by rw [hB, Function.update_of_ne (by decide : (7:ℕ) ≠ 10), hA7]
  have hB10 : memB 10 = (mem 10 * mem 10) % mem 8 := by rw [hB, Function.update_self, hA10, hA8]
  have hC8 : memC 8 = mem 8 := by rw [hC, Function.update_of_ne (by decide : (8:ℕ) ≠ 10), hB8]
  have hC10 : memC 10 = memB 10 * mem 7 := by rw [hC, Function.update_self, hB7]
  have hD10 : memD 10 = memC 10 % memC 8 := by rw [hD, Function.update_self]
  have hD22 : memD 22 = mem 22 := by
    rw [hD, Function.update_of_ne (by decide : (22:ℕ) ≠ 10), hC, Function.update_of_ne (by decide : (22:ℕ) ≠ 10),
        hB, Function.update_of_ne (by decide : (22:ℕ) ≠ 10), hA, Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]
  have hD3 : memD 3 = mem 3 := by
    rw [hD, Function.update_of_ne (by decide : (3:ℕ) ≠ 10), hC, Function.update_of_ne (by decide : (3:ℕ) ≠ 10),
        hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 10), hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]
  have hE10 : memE 10 = memD 10 := by rw [hE, Function.update_of_ne (by decide : (10:ℕ) ≠ 22)]
  have hE22 : memE 22 = memD 22 - memD 3 := by rw [hE, Function.update_self]
  have hrun : Lrun 6 ⟨11, mem⟩ = ⟨10, memE⟩ := by
    rw [show (6:ℕ) = 5+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst11, ← hA, Lst12, ← hB, Lst13, ← hC, Lst14, ← hD, Lst15, ← hE, Lst16]
  refine ⟨memE, hrun, ?_, ?_, ?_⟩
  · rw [hE10, hD10, hC8, hC10, hB10]
  · rw [hE22, hD22, hD3]
  · intro i hi1 hi2
    rw [hE, Function.update_of_ne (by omega : i ≠ 22), hD, Function.update_of_ne (by omega : i ≠ 10),
        hC, Function.update_of_ne (by omega : i ≠ 10), hB, Function.update_of_ne (by omega : i ≠ 10),
        hA, Function.update_of_ne (by omega : i ≠ 10)]

/-! ## The inverse loop -/

theorem pre_inv (r k : ℕ) :
    k ≤ r → ∀ (mem : ℕ → ℤ), mem 22 = (k:ℤ) → mem 2 = 0 → mem 3 = 1 → mem 7 = 5 →
      mem 8 = (((2:ℕ)^r : ℕ):ℤ) → 0 ≤ mem 10 → mem 10 < (((2:ℕ)^r : ℕ):ℤ) →
      ∃ t ≤ 7*k + 2, ∃ mem', Lrun t ⟨10, mem⟩ = ⟨17, mem'⟩ ∧
        ((mem' 10 : ℤ) : ZMod (2^r)) = (((mem 10 : ℤ) : ZMod (2^r)))^(2^k) * (5 : ZMod (2^r))^(2^k - 1) ∧
        0 ≤ mem' 10 ∧ mem' 10 < (((2:ℕ)^r : ℕ):ℤ) ∧
        (∀ i, i ≠ 10 → i ≠ 22 → mem' i = mem i) := by
  induction k with
  | zero =>
    intro hk mem h22 h2 h3 h7 h8 h10n h10u
    refine ⟨1, by omega, mem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Lrun_succ, Lrun_zero]; rw [Lst10eq _ (by simp [h22, h2])]
    · rw [show (((2:ℕ)^0)) = 1 by norm_num, pow_one, Nat.sub_self, pow_zero, mul_one]
    · exact h10n
    · exact h10u
    · intro i _ _; rfl
  | succ k ih =>
    intro hk mem h22 h2 h3 h7 h8 h10n h10u
    have hne : mem 22 ≠ mem 2 := by rw [h22, h2]; exact_mod_cast Nat.succ_ne_zero k
    obtain ⟨memE, hrunE, hE10, hE22, hEfr⟩ := s_body mem
    have hE22' : memE 22 = (k : ℤ) := by rw [hE22, h22, h3]; push_cast; ring
    have hE2 : memE 2 = 0 := by rw [hEfr 2 (by decide) (by decide)]; exact h2
    have hE3 : memE 3 = 1 := by rw [hEfr 3 (by decide) (by decide)]; exact h3
    have hE7 : memE 7 = 5 := by rw [hEfr 7 (by decide) (by decide)]; exact h7
    have hE8 : memE 8 = (((2:ℕ)^r : ℕ):ℤ) := by rw [hEfr 8 (by decide) (by decide)]; exact h8
    have hMpos : (0:ℤ) < (((2:ℕ)^r : ℕ):ℤ) := by exact_mod_cast (two_pow_pos r)
    have hE10n : 0 ≤ memE 10 := by
      rw [hE10, h8]; exact Int.emod_nonneg _ (ne_of_gt hMpos)
    have hE10u : memE 10 < (((2:ℕ)^r : ℕ):ℤ) := by
      rw [hE10, h8]; exact Int.emod_lt_of_pos _ hMpos
    have hE10z : ((memE 10 : ℤ) : ZMod (2^r)) = (((mem 10 : ℤ) : ZMod (2^r)))^2 * 5 := by
      rw [hE10, h8, h7, intCast_emod, Int.cast_mul, intCast_emod, Int.cast_mul,
          show ((5:ℤ) : ZMod (2^r)) = 5 by norm_num]
      ring
    obtain ⟨t, ht, memF, hrunF, hF10, hF10n, hF10u, hFfr⟩ :=
      ih (by omega) memE hE22' hE2 hE3 hE7 hE8 hE10n hE10u
    have hstep : Lrun 7 ⟨10, mem⟩ = ⟨10, memE⟩ := by
      rw [show (7:ℕ) = 1 + 6 by omega, Lrun_add,
          show Lrun 1 ⟨10, mem⟩ = ⟨11, mem⟩ from by
            simp only [Lrun_succ, Lrun_zero]; rw [Lst10ne mem hne], hrunE]
    refine ⟨7 + t, by omega, memF, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Lrun_add, hstep]; exact hrunF
    · rw [hF10,
          show (((memE 10 : ℤ) : ZMod (2^r))^(2^k)) * (5 : ZMod (2^r))^(2^k - 1)
            = (((mem 10 : ℤ) : ZMod (2^r)))^(2^(k+1)) * (5 : ZMod (2^r))^(2^(k+1)-1) from by
            rw [hE10z, mul_pow, ← pow_mul,
                show (2:ℕ) * 2^k = 2^(k+1) by rw [← Nat.pow_succ'],
                mul_assoc, ← pow_add,
                show 2^k + (2^k - 1) = 2^(k+1) - 1 by
                  have h1 : 1 ≤ (2:ℕ)^k := Nat.one_le_two_pow
                  have h2 : (2:ℕ)^(k+1) = 2^k + 2^k := by rw [Nat.pow_succ']; ring
                  omega]]
    · exact hF10n
    · exact hF10u
    · intro i hi1 hi2
      rw [hFfr i hi1 hi2, hEfr i hi1 hi2]

/-! ## The squaring loop and the number-theoretic core of the main loop -/

/-- `sZ r = 5^(-1) = 5^(2^(r-2)-1)` in `ZMod (2^r)`. -/
def sZ (r : ℕ) : ZMod (2^r) := (5 : ZMod (2^r))^(2^(r-2) - 1)

theorem five_mul_sZ (r : ℕ) (hr : 2 ≤ r) : (5 : ZMod (2^r)) * sZ r = 1 := by
  rw [sZ, mul_comm]; exact five_inv r hr

theorem neg_one_pow_two_pow (r k : ℕ) (hk : 1 ≤ k) : (-1 : ZMod (2^r)) ^ (2^k) = 1 := by
  rw [show (2:ℕ)^k = 2 * 2^(k-1) by rw [← pow_succ']; congr 1; omega, pow_mul]
  norm_num

theorem neg_one_pow_mul_two_pow (r j k : ℕ) (hk : 1 ≤ k) :
    (-1 : ZMod (2^r)) ^ (j * 2^k) = 1 := by
  rw [mul_comm, pow_mul, neg_one_pow_two_pow r k hk, one_pow]

/-- The order-two element `5^(2^(r-3)) = 2^(r-1)+1` raised to the `i`-th bit of `h`. -/
def Hb (r h i : ℕ) : ZMod (2^r) := ((5 : ZMod (2^r))^(2^(r-3)))^((h / 2^i) % 2)

theorem Hb_zero_or_one (r h i : ℕ) (hr : 3 ≤ r) :
    Hb r h i = 1 ∨ Hb r h i = (((1 + 2^(r-1) : ℕ)) : ZMod (2^r)) := by
  have hlt : (h / 2^i) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : (h / 2^i) % 2 = 0 ∨ (h / 2^i) % 2 = 1) with h | h
  · left; rw [Hb, h, pow_zero]
  · right; rw [Hb, h, pow_one, five_pow_ord2 r hr]

/-- The squaring inner loop: from `⟨27,·⟩` with `mem 20 = mem 21 + e` and `mem 19 = x`, after
`4*e + 2` steps we reach `⟨33,·⟩` with `mem 19 = x^(2^e) mod 2^r`. -/
theorem sq_loop (r e : ℕ) :
    ∀ (x : ℤ) (mem : ℕ → ℤ), 0 ≤ x → x < (((2^r : ℕ)) : ℤ) → mem 19 = x → mem 20 = mem 21 + (e : ℤ) →
      mem 8 = (((2^r : ℕ)) : ℤ) → mem 2 = 0 → mem 3 = 1 →
      ∃ mem', Lrun (5 * e + 2) ⟨27, mem⟩ = ⟨33, mem'⟩ ∧
        ((mem' 19 : ℤ) : ZMod (2^r)) = ((x : ℤ) : ZMod (2^r)) ^ (2^e) ∧
        (0 ≤ mem' 19 ∧ mem' 19 < (((2^r : ℕ)) : ℤ)) ∧
        mem' 20 = mem 20 ∧ mem' 21 = mem 21 + (e : ℤ) ∧
        (∀ i, i ≠ 19 → i ≠ 21 → mem' i = mem i) := by
  induction e with
  | zero =>
    intro x mem hx0 hxu h19 h20 h8 h2 h3
    refine ⟨mem, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · rw [show (5*0+2:ℕ) = 1+1 from rfl, Lrun_succ, Lrun_succ, Lrun_zero]
      rw [Lst27le _ (by rw [h20]; push_cast; linarith), Lst28]
    · rw [h19, pow_zero, pow_one]
    · rw [h19]; exact ⟨hx0, hxu⟩
    · rw [Nat.cast_zero, add_zero]
    · intro i _ _; rfl
  | succ e ih =>
    intro x mem hx0 hxu h19 h20 h8 h2 h3
    have hMpos : (0:ℤ) < (((2^r : ℕ)) : ℤ) := by positivity
    have hgt : mem 20 > mem 21 := by
      rw [h20]; push_cast; linarith [Int.natCast_nonneg e]
    set A : ℕ → ℤ := Function.update mem 19 (mem 19 * mem 19) with hA
    set B : ℕ → ℤ := Function.update A 19 (A 19 % A 8) with hB
    set C : ℕ → ℤ := Function.update B 21 (B 21 + B 3) with hC
    have hA8 : A 8 = (((2^r : ℕ)) : ℤ) := by
      rw [hA, Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact h8
    have hA19 : A 19 = mem 19 * mem 19 := by rw [hA, Function.update_self]
    have hA21 : A 21 = mem 21 := by rw [hA, Function.update_of_ne (by decide : (21:ℕ) ≠ 19)]
    have hA3 : A 3 = mem 3 := by rw [hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 19)]
    have hB19 : B 19 = A 19 % A 8 := by rw [hB, Function.update_self]
    have hB8 : B 8 = A 8 := by rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 19), hA8]
    have hB21 : B 21 = mem 21 := by rw [hB, Function.update_of_ne (by decide : (21:ℕ) ≠ 19), hA21]
    have hB3 : B 3 = mem 3 := by rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 19), hA3]
    have hB20 : B 20 = mem 20 := by
      rw [hB, Function.update_of_ne (by decide : (20:ℕ) ≠ 19), hA, Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]
    have hC19 : C 19 = B 19 := by rw [hC, Function.update_of_ne (by decide : (19:ℕ) ≠ 21)]
    have hC21 : C 21 = mem 21 + 1 := by
      rw [hC, Function.update_self, hB21, hB3, h3]
    have hC8 : C 8 = (((2^r : ℕ)) : ℤ) := by
      rw [hC, Function.update_of_ne (by decide : (8:ℕ) ≠ 21), hB8, hA8]
    have hC2 : C 2 = 0 := by
      rw [hC, Function.update_of_ne (by decide : (2:ℕ) ≠ 21), hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 19),
          hA, Function.update_of_ne (by decide : (2:ℕ) ≠ 19)]; exact h2
    have hC3 : C 3 = 1 := by
      rw [hC, Function.update_of_ne (by decide : (3:ℕ) ≠ 21), hB3]; exact h3
    have hC20 : C 20 = mem 20 := by
      rw [hC, Function.update_of_ne (by decide : (20:ℕ) ≠ 21), hB20]
    have e4 : Lrun 5 ⟨27, mem⟩ = ⟨27, C⟩ := by
      rw [show (5:ℕ) = 4+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
      rw [Lst27gt mem hgt, Lst29, ← hA, Lst30, ← hB, Lst31, ← hC, Lst32]
    have h20C : C 20 = C 21 + (e : ℤ) := by rw [hC20, hC21, h20]; push_cast; ring
    have hC19n : 0 ≤ C 19 := by rw [hC19, hB19, hA8]; exact Int.emod_nonneg _ (ne_of_gt hMpos)
    have hC19u : C 19 < (((2^r : ℕ)) : ℤ) := by rw [hC19, hB19, hA8]; exact Int.emod_lt_of_pos _ hMpos
    obtain ⟨mem', hrun', hz', hb', h20', h21', hfr'⟩ := ih (C 19) C hC19n hC19u hC19 h20C hC8 hC2 hC3
    refine ⟨mem', ?_, ?_, hb', ?_, ?_, ?_⟩
    · rw [show (5 * (e+1) + 2 : ℕ) = 5 + (5*e+2) by ring, Lrun_add, e4, hrun']
    · rw [hz', hC19, hB19, hA19, hA8, intCast_emod r (mem 19 * mem 19), h19]
      rw [show ((x * x : ℤ) : ZMod (2^r)) = (x : ZMod (2^r)) * (x : ZMod (2^r)) by push_cast; ring,
          mul_pow, show (2:ℕ)^(e+1) = 2^e * 2 by rw [pow_succ], pow_mul, pow_two]
    · rw [h20', hC20]
    · rw [h21', hC21]; push_cast; ring
    · intro i hi1 hi2
      rw [hfr' i hi1 hi2, hC, Function.update_of_ne (by omega : i ≠ 21), hB,
          Function.update_of_ne (by omega : i ≠ 19), hA, Function.update_of_ne (by omega : i ≠ 19)]


/-! ## Binary-digit bookkeeping and the arithmetic core of one loop iteration -/

theorem mod_two_pow_succ (n i : ℕ) : n % 2^(i+1) = n % 2^i + (n / 2^i) % 2 * 2^i := by
  have hdecomp : (n % 2^(i+1)) / 2^i * 2^i + (n % 2^(i+1)) % 2^i = n % 2^(i+1) := Nat.div_add_mod' _ _
  rw [Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (by omega : i ≤ i + 1)),
      show (n % 2^(i+1)) / 2^i = (n / 2^i) % 2 by
        rw [← Nat.mod_mul_right_div_self n (2^i) 2, show 2^i * 2 = 2^(i+1) by rw [pow_succ]]] at hdecomp
  rw [← hdecomp, add_comm]

theorem bit_one_mod (h i : ℕ) (hb : (h / 2^i) % 2 = 1) :
    ((h % 2^i : ℕ) : ℤ) + ((2^i : ℕ) : ℤ) = ((h % 2^(i+1) : ℕ) : ℤ) := by
  have hh := mod_two_pow_succ h i
  rw [hb] at hh; norm_num at hh
  rw [hh]; push_cast; ring

theorem bit_zero_mod (h i : ℕ) (hb : (h / 2^i) % 2 = 0) :
    ((h % 2^i : ℕ) : ℤ) = ((h % 2^(i+1) : ℕ) : ℤ) := by
  have hh := mod_two_pow_succ h i
  rw [hb] at hh; norm_num at hh
  rw [hh]

theorem two_pow_succ_cast (i : ℕ) :
    ((2^i : ℕ) : ℤ) + ((2^i : ℕ) : ℤ) = ((2^(i+1) : ℕ) : ℤ) := by
  rw [← Nat.cast_add, show (2:ℕ)^i + 2^i = 2^(i+1) by rw [pow_succ]; ring]

theorem eq_of_cast_eq (r : ℕ) (y b : ℤ) (hy : 0 ≤ y) (hyu : y < (((2^r : ℕ)) : ℤ))
    (hb : 0 ≤ b) (hbu : b < (((2^r : ℕ)) : ℤ)) (h : ((y : ℤ) : ZMod (2^r)) = ((b : ℤ) : ZMod (2^r))) :
    y = b := by
  rw [ZMod.intCast_eq_intCast_iff'] at h
  rwa [Int.emod_eq_of_lt hy hyu, Int.emod_eq_of_lt hb hbu] at h

theorem one_lt_H (r : ℕ) (hr : 1 ≤ r) : (1 : ℤ) < (((1 + 2^(r-1) : ℕ)) : ℤ) := by
  have h : (0 : ℕ) < 2^(r-1) := two_pow_pos _
  have h2 : (1 : ℕ) < 1 + 2^(r-1) := by omega
  exact_mod_cast h2

theorem H_lt_M (r : ℕ) (hr : 2 ≤ r) : (((1 + 2^(r-1) : ℕ)) : ℤ) < (((2^r : ℕ)) : ℤ) := by
  have h : (1 + 2^(r-1) : ℕ) < 2^r := lt_two_pow r hr
  exact_mod_cast h

theorem neg_one_ne_one (r : ℕ) (hr : 2 ≤ r) : (-1 : ZMod (2^r)) ≠ 1 := by
  intro h
  apply two_ne_zero r hr
  have hh := congrArg (fun x : ZMod (2^r) => x + 1) h
  simp only [neg_add_cancel] at hh
  rw [show (2 : ZMod (2^r)) = 1 + 1 by norm_num]
  exact hh.symm

/-- The arithmetic core of one loop iteration: from `⟨20,·⟩` (with the loop's runtime values)
after `8 + 5*(r-3-i)` steps the machine reaches `⟨33,·⟩` with `mem 19` congruent to
`(-1)^(j·2^(r-3-i)) · Hb r h i`. -/
theorem iter_core (r j h i p : ℕ) (hr : 3 ≤ r) (hi : i < r - 2) (mem : ℕ → ℤ)
    (h1 : mem 1 = (p : ℤ)) (h2 : mem 2 = 0) (h3 : mem 3 = 1)
    (h8 : mem 8 = (((2^r : ℕ)) : ℤ))
    (h13 : mem 13 = ((r - 2 - i : ℕ) : ℤ))
    (h14 : ((mem 14 : ℤ) : ZMod (2^r)) = (sZ r) ^ (h % 2^i))
    (hp : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ j * (5 : ZMod (2^r)) ^ h) :
    ∃ mem3, Lrun (8 + 5 * (r - 3 - i)) ⟨20, mem⟩ = ⟨33, mem3⟩ ∧
      ((mem3 19 : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ (j * 2^(r-3-i)) * Hb r h i ∧
      (0 ≤ mem3 19 ∧ mem3 19 < (((2^r : ℕ)) : ℤ)) ∧
      (∀ k, k ≠ 18 → k ≠ 19 → k ≠ 20 → k ≠ 21 → mem3 k = mem k) := by
  have h13ge : 1 ≤ r - 2 - i := by omega
  have hgt : mem 13 > mem 2 := by rw [h2, h13]; exact_mod_cast h13ge
  set A : ℕ → ℤ := Function.update mem 18 (mem 14 * mem 1) with hA
  set B : ℕ → ℤ := Function.update A 18 (A 18 % A 8) with hB
  set C : ℕ → ℤ := Function.update B 20 (B 13 - B 3) with hC
  set D : ℕ → ℤ := Function.update C 19 (C 18 + C 2) with hD
  set E : ℕ → ℤ := Function.update D 21 (D 2 + D 2) with hE
  have hA8 : A 8 = (((2^r : ℕ)) : ℤ) := by rw [hA, Function.update_of_ne (by decide : (8:ℕ) ≠ 18)]; exact h8
  have hA18 : A 18 = mem 14 * mem 1 := by rw [hA, Function.update_self]
  have hA13 : A 13 = mem 13 := by rw [hA, Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]
  have hA3 : A 3 = mem 3 := by rw [hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 18)]
  have hA2 : A 2 = mem 2 := by rw [hA, Function.update_of_ne (by decide : (2:ℕ) ≠ 18)]
  have hB18 : B 18 = A 18 % A 8 := by rw [hB, Function.update_self]
  have hB13 : B 13 = mem 13 := by rw [hB, Function.update_of_ne (by decide : (13:ℕ) ≠ 18), hA13]
  have hB3 : B 3 = mem 3 := by rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 18), hA3]
  have hB2 : B 2 = mem 2 := by rw [hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 18), hA2]
  have hB8 : B 8 = (((2^r : ℕ)) : ℤ) := by rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 18), hA8]
  have hC20 : C 20 = mem 13 - mem 3 := by rw [hC, Function.update_self, hB13, hB3]
  have hC18 : C 18 = A 18 % A 8 := by rw [hC, Function.update_of_ne (by decide : (18:ℕ) ≠ 20), hB18]
  have hC2 : C 2 = mem 2 := by rw [hC, Function.update_of_ne (by decide : (2:ℕ) ≠ 20), hB2]
  have hD19 : D 19 = A 18 % A 8 + mem 2 := by rw [hD, Function.update_self, hC18, hC2]
  have hD20 : D 20 = mem 13 - mem 3 := by rw [hD, Function.update_of_ne (by decide : (20:ℕ) ≠ 19), hC20]
  have hD2 : D 2 = mem 2 := by rw [hD, Function.update_of_ne (by decide : (2:ℕ) ≠ 19), hC2]
  have hE19 : E 19 = (mem 14 * mem 1) % (((2^r : ℕ)) : ℤ) := by rw [hE, Function.update_of_ne (by decide : (19:ℕ) ≠ 21), hD19, hA18, hA8, h2, add_zero]
  have hE20 : E 20 = ((r - 3 - i : ℕ) : ℤ) := by
    rw [hE, Function.update_of_ne (by decide : (20:ℕ) ≠ 21), hD20, h13, h3]
    push_cast; omega
  have hE21 : E 21 = 0 := by rw [hE, Function.update_self, hD2, h2]; ring
  have hE8 : E 8 = (((2^r : ℕ)) : ℤ) := by rw [hE, Function.update_of_ne (by decide : (8:ℕ) ≠ 21), hD, Function.update_of_ne (by decide : (8:ℕ) ≠ 19), hC, Function.update_of_ne (by decide : (8:ℕ) ≠ 20), hB8]
  have hE2 : E 2 = 0 := by rw [hE, Function.update_of_ne (by decide : (2:ℕ) ≠ 21), hD2, h2]
  have hE3 : E 3 = 1 := by rw [hE, Function.update_of_ne (by decide : (3:ℕ) ≠ 21), hD, Function.update_of_ne (by decide : (3:ℕ) ≠ 19), hC, Function.update_of_ne (by decide : (3:ℕ) ≠ 20), hB3, h3]
  have hEfr : ∀ k, k ≠ 18 → k ≠ 19 → k ≠ 20 → k ≠ 21 → E k = mem k := by
    intro k a b c d
    rw [hE, Function.update_of_ne d, hD, Function.update_of_ne b, hC, Function.update_of_ne c,
        hB, Function.update_of_ne a, hA, Function.update_of_ne a]
  have hrun6 : Lrun 6 ⟨20, mem⟩ = ⟨27, E⟩ := by
    rw [show (6:ℕ) = 5+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst20gt mem hgt, Lst22, ← hA, Lst23, ← hB, Lst24, ← hC, Lst25, ← hD, Lst26, ← hE]
  have hE19' : E 20 = E 21 + ((r - 3 - i : ℕ) : ℤ) := by rw [hE20, hE21, zero_add]
  have hMpos : (0:ℤ) < (((2^r : ℕ)) : ℤ) := by positivity
  have hEx0 : 0 ≤ E 19 := by rw [hE19]; exact Int.emod_nonneg _ (ne_of_gt hMpos)
  have hExu : E 19 < (((2^r : ℕ)) : ℤ) := by rw [hE19]; exact Int.emod_lt_of_pos _ hMpos
  obtain ⟨mem3, hrunS, hzS, hbS, -, -, hfrS⟩ :=
    sq_loop r (r - 3 - i) (E 19) E hEx0 hExu rfl hE19' hE8 hE2 hE3
  have hxZ : ((E 19 : ℤ) : ZMod (2^r)) = (sZ r) ^ (h % 2^i) * ((-1 : ZMod (2^r)) ^ j * (5 : ZMod (2^r)) ^ h) := by
    rw [hE19, intCast_emod r (mem 14 * mem 1), Int.cast_mul, h14, h1, hp]
  have hstep : ((sZ r) ^ (h % 2^i) * ((-1 : ZMod (2^r)) ^ j * (5 : ZMod (2^r)) ^ h)) ^ (2^(r-3-i))
      = (-1 : ZMod (2^r)) ^ (j * 2^(r-3-i)) * Hb r h i := by
    rw [mul_comm ((sZ r) ^ (h % 2^i)) ((-1 : ZMod (2^r)) ^ j * (5 : ZMod (2^r)) ^ h),
        main_pow2 r hr (sZ r) (five_mul_sZ r (by omega)) h j i (by omega : i ≤ r - 3)]
    rfl
  refine ⟨mem3, ?_, ?_, hbS, ?_⟩
  · rw [show (8 + 5 * (r - 3 - i)) = 6 + (5 * (r - 3 - i) + 2) by ring, Lrun_add, hrun6, hrunS]
  · rw [hzS, hxZ, hstep]
  · intro k a b c d
    rw [hfrS k b d, hEfr k a b c d]


theorem bit_zero_mod_nat (h i : ℕ) (hb : (h / 2^i) % 2 = 0) : h % 2^i = h % 2^(i+1) := by
  have := mod_two_pow_succ h i; rw [hb] at this; simpa using this.symm

theorem bit_one_mod_nat (h i : ℕ) (hb : (h / 2^i) % 2 = 1) : h % 2^i + 2^i = h % 2^(i+1) := by
  have := mod_two_pow_succ h i; rw [hb] at this; simpa using this.symm

/-- The loop invariant at `⟨20,·⟩`: `mem 13` counts down from `r-2`, `mem 15` accumulates the
low `i` bits of `h`, `mem 14 = s^(h mod 2^i)`, `mem 16 = s^(2^i)`, `mem 17 = 2^i`. -/
def LoopInv (r p h i : ℕ) (mem : ℕ → ℤ) : Prop :=
  mem 0 = (r : ℤ) ∧ mem 1 = (p : ℤ) ∧ mem 2 = 0 ∧ mem 3 = 1 ∧ mem 4 = 2 ∧
  mem 7 = 5 ∧ mem 8 = (((2^r : ℕ)) : ℤ) ∧ mem 9 = (((1 + 2^(r-1) : ℕ)) : ℤ) ∧
  mem 13 = ((r - 2 - i : ℕ) : ℤ) ∧
  mem 15 = ((h % 2^i : ℕ) : ℤ) ∧
  mem 17 = (((2^i : ℕ)) : ℤ) ∧
  mem 24 = -1 ∧
  ((mem 14 : ℤ) : ZMod (2^r)) = (sZ r) ^ (h % 2^i) ∧
  ((mem 16 : ℤ) : ZMod (2^r)) = (sZ r) ^ (2^i) ∧
  (0 ≤ mem 14 ∧ mem 14 < (((2^r : ℕ)) : ℤ)) ∧
  (0 ≤ mem 16 ∧ mem 16 < (((2^r : ℕ)) : ℤ)) ∧
  0 ≤ mem 15 ∧ 0 ≤ mem 17 ∧
  i ≤ r - 2

theorem iter_post (mem : ℕ → ℤ) :
    ∃ mem', Lrun 5 ⟨41, mem⟩ = ⟨20, mem'⟩ ∧
      mem' 16 = (mem 16 * mem 16) % mem 8 ∧
      mem' 17 = mem 17 + mem 17 ∧
      mem' 13 = mem 13 - mem 3 ∧
      (∀ k, k ≠ 13 → k ≠ 16 → k ≠ 17 → mem' k = mem k) := by
  set A : ℕ → ℤ := Function.update mem 16 (mem 16 * mem 16) with hA
  set B : ℕ → ℤ := Function.update A 16 (A 16 % A 8) with hB
  set C : ℕ → ℤ := Function.update B 17 (B 17 + B 17) with hC
  set D : ℕ → ℤ := Function.update C 13 (C 13 - C 3) with hD
  have hA8 : A 8 = mem 8 := by rw [hA, Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]
  have hA16 : A 16 = mem 16 * mem 16 := by rw [hA, Function.update_self]
  have hA17 : A 17 = mem 17 := by rw [hA, Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]
  have hA3 : A 3 = mem 3 := by rw [hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 16)]
  have hA13 : A 13 = mem 13 := by rw [hA, Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]
  have hB16 : B 16 = A 16 % A 8 := by rw [hB, Function.update_self]
  have hB17 : B 17 = mem 17 := by rw [hB, Function.update_of_ne (by decide : (17:ℕ) ≠ 16), hA17]
  have hB3 : B 3 = mem 3 := by rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 16), hA3]
  have hB13 : B 13 = mem 13 := by rw [hB, Function.update_of_ne (by decide : (13:ℕ) ≠ 16), hA13]
  have hC17 : C 17 = mem 17 + mem 17 := by rw [hC, Function.update_self, hB17]
  have hC3 : C 3 = mem 3 := by rw [hC, Function.update_of_ne (by decide : (3:ℕ) ≠ 17), hB3]
  have hC13 : C 13 = mem 13 := by rw [hC, Function.update_of_ne (by decide : (13:ℕ) ≠ 17), hB13]
  have hC16 : C 16 = A 16 % A 8 := by rw [hC, Function.update_of_ne (by decide : (16:ℕ) ≠ 17), hB16]
  have hD13 : D 13 = mem 13 - mem 3 := by rw [hD, Function.update_self, hC13, hC3]
  have hD16 : D 16 = (mem 16 * mem 16) % mem 8 := by rw [hD, Function.update_of_ne (by decide : (16:ℕ) ≠ 13), hC16, hA16, hA8]
  have hD17 : D 17 = mem 17 + mem 17 := by rw [hD, Function.update_of_ne (by decide : (17:ℕ) ≠ 13), hC17]
  have hrun : Lrun 5 ⟨41, mem⟩ = ⟨20, D⟩ := by
    rw [show (5:ℕ) = 4+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst41, ← hA, Lst42, ← hB, Lst43, ← hC, Lst44, ← hD, Lst45]
  refine ⟨D, hrun, hD16, hD17, hD13, ?_⟩
  intro k hk13 hk16 hk17
  rw [hD, Function.update_of_ne hk13, hC, Function.update_of_ne hk17, hB, Function.update_of_ne hk16,
      hA, Function.update_of_ne hk16]

theorem iter_bit0 (mem : ℕ → ℤ) (h19 : mem 19 = mem 3) :
    ∃ mem', Lrun 7 ⟨33, mem⟩ = ⟨20, mem'⟩ ∧
      mem' 14 = mem 14 ∧ mem' 15 = mem 15 ∧
      mem' 16 = (mem 16 * mem 16) % mem 8 ∧ mem' 17 = mem 17 + mem 17 ∧
      mem' 13 = mem 13 - mem 3 ∧
      (∀ k, k ≠ 13 → k ≠ 16 → k ≠ 17 → mem' k = mem k) := by
  have h2 : Lrun 2 ⟨33, mem⟩ = ⟨41, mem⟩ := by
    rw [show (2:ℕ) = 1+1 from rfl, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst33eq mem h19, Lst40]
  obtain ⟨mem', hrun', h16, h17, h13, hfr⟩ := iter_post mem
  refine ⟨mem', ?_, ?_, ?_, h16, h17, h13, hfr⟩
  · rw [show (7:ℕ) = 2 + 5 by norm_num, Lrun_add, h2, hrun']
  · rw [hfr 14 (by decide) (by decide) (by decide)]
  · rw [hfr 15 (by decide) (by decide) (by decide)]

theorem iter_bit1 (mem : ℕ → ℤ) (h19 : mem 19 = mem 9) (h9ne : mem 9 ≠ mem 3) :
    ∃ mem', Lrun 11 ⟨33, mem⟩ = ⟨20, mem'⟩ ∧
      mem' 14 = (mem 14 * mem 16) % mem 8 ∧ mem' 15 = mem 15 + mem 17 ∧
      mem' 16 = (mem 16 * mem 16) % mem 8 ∧ mem' 17 = mem 17 + mem 17 ∧
      mem' 13 = mem 13 - mem 3 ∧
      (∀ k, k ≠ 13 → k ≠ 14 → k ≠ 15 → k ≠ 16 → k ≠ 17 → mem' k = mem k) := by
  have hne : mem 19 ≠ mem 3 := by rw [h19]; exact h9ne
  set A : ℕ → ℤ := Function.update mem 15 (mem 15 + mem 17) with hA
  set B : ℕ → ℤ := Function.update A 14 (A 14 * A 16) with hB
  set C : ℕ → ℤ := Function.update B 14 (B 14 % B 8) with hC
  have hA15 : A 15 = mem 15 + mem 17 := by rw [hA, Function.update_self]
  have hA14 : A 14 = mem 14 := by rw [hA, Function.update_of_ne (by decide : (14:ℕ) ≠ 15)]
  have hA16 : A 16 = mem 16 := by rw [hA, Function.update_of_ne (by decide : (16:ℕ) ≠ 15)]
  have hA8 : A 8 = mem 8 := by rw [hA, Function.update_of_ne (by decide : (8:ℕ) ≠ 15)]
  have hA17 : A 17 = mem 17 := by rw [hA, Function.update_of_ne (by decide : (17:ℕ) ≠ 15)]
  have hA13 : A 13 = mem 13 := by rw [hA, Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]
  have hA3 : A 3 = mem 3 := by rw [hA, Function.update_of_ne (by decide : (3:ℕ) ≠ 15)]
  have hB14 : B 14 = mem 14 * mem 16 := by rw [hB, Function.update_self, hA14, hA16]
  have hB8 : B 8 = mem 8 := by rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 14), hA8]
  have hB15 : B 15 = mem 15 + mem 17 := by rw [hB, Function.update_of_ne (by decide : (15:ℕ) ≠ 14), hA15]
  have hB16 : B 16 = mem 16 := by rw [hB, Function.update_of_ne (by decide : (16:ℕ) ≠ 14), hA16]
  have hB17 : B 17 = mem 17 := by rw [hB, Function.update_of_ne (by decide : (17:ℕ) ≠ 14), hA17]
  have hB13 : B 13 = mem 13 := by rw [hB, Function.update_of_ne (by decide : (13:ℕ) ≠ 14), hA13]
  have hB3 : B 3 = mem 3 := by rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 14), hA3]
  have hC14 : C 14 = (mem 14 * mem 16) % mem 8 := by rw [hC, Function.update_self, hB14, hB8]
  have hC8 : C 8 = mem 8 := by rw [hC, Function.update_of_ne (by decide : (8:ℕ) ≠ 14), hB8]
  have hC15 : C 15 = mem 15 + mem 17 := by rw [hC, Function.update_of_ne (by decide : (15:ℕ) ≠ 14), hB15]
  have hC16 : C 16 = mem 16 := by rw [hC, Function.update_of_ne (by decide : (16:ℕ) ≠ 14), hB16]
  have hC17 : C 17 = mem 17 := by rw [hC, Function.update_of_ne (by decide : (17:ℕ) ≠ 14), hB17]
  have hC13 : C 13 = mem 13 := by rw [hC, Function.update_of_ne (by decide : (13:ℕ) ≠ 14), hB13]
  have hC3 : C 3 = mem 3 := by rw [hC, Function.update_of_ne (by decide : (3:ℕ) ≠ 14), hB3]
  have h6 : Lrun 6 ⟨33, mem⟩ = ⟨41, C⟩ := by
    rw [show (6:ℕ) = 5+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst33ne mem hne, Lst34eq mem h19, Lst36, ← hA, Lst37, ← hB, Lst38, ← hC, Lst39]
  obtain ⟨mem', hrun', h16, h17, h13, hfr⟩ := iter_post C
  refine ⟨mem', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (11:ℕ) = 6 + 5 by norm_num, Lrun_add, h6, hrun']
  · rw [hfr 14 (by decide) (by decide) (by decide)]; exact hC14
  · rw [hfr 15 (by decide) (by decide) (by decide), hC15]
  · rw [h16, hC16, hC8]
  · rw [h17, hC17]
  · rw [h13, hC13, hC3]
  · intro k a b c d e
    rw [hfr k a d e, hC, Function.update_of_ne b, hB, Function.update_of_ne b, hA, Function.update_of_ne c]

theorem iter_fail (mem : ℕ → ℤ) (h3 : mem 19 ≠ mem 3) (h9 : mem 19 ≠ mem 9) :
    ∃ mem', Lrun 3 ⟨33, mem⟩ = ⟨48, mem'⟩ ∧ mem' = mem := by
  refine ⟨mem, ?_, rfl⟩
  rw [show (3:ℕ) = 2+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
  rw [Lst33ne mem h3, Lst34ne mem h9, Lst35]


/-- One successful loop iteration (the sign `(-1)^(j·2^(r-3-i))` is `+1`). -/
theorem loop_step (r p j h i : ℕ) (hr : 3 ≤ r) (hi : i < r - 2) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ j * (5 : ZMod (2^r)) ^ h)
    (hsign : (-1 : ZMod (2^r)) ^ (j * 2^(r-3-i)) = 1) :
    ∀ mem, LoopInv r p h i mem →
      ∃ t ≤ 5 * (r - 3 - i) + 20, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨20, mem'⟩ ∧ LoopInv r p h (i+1) mem' := by
  intro mem hL
  obtain ⟨h0, h1, h2, h3, h4, h7, h8, h9, h13, h15, h17, h24, h14, h16, h14b, h16b, h15n, h17n, hile⟩ := hL
  obtain ⟨mem3, hrun3, hz3, hb3, hfr3⟩ := iter_core r j h i p hr hi mem h1 h2 h3 h8 h13 h14 hp
  have hMpos : (0:ℤ) < (((2^r : ℕ)) : ℤ) := by positivity
  have frame3 : ∀ k, k < 18 → mem3 k = mem k :=
    fun k hk => hfr3 k (by omega) (by omega) (by omega) (by omega)
  have h24' : mem3 24 = -1 := by rw [hfr3 24 (by decide) (by decide) (by decide) (by decide), h24]
  have hz3' : ((mem3 19 : ℤ) : ZMod (2^r)) = Hb r h i := by rw [hz3, hsign, one_mul]
  have e0 : mem3 0 = (r : ℤ) := by rw [frame3 0 (by norm_num), h0]
  have e1 : mem3 1 = (p : ℤ) := by rw [frame3 1 (by norm_num), h1]
  have e2 : mem3 2 = 0 := by rw [frame3 2 (by norm_num), h2]
  have e3 : mem3 3 = 1 := by rw [frame3 3 (by norm_num), h3]
  have e4 : mem3 4 = 2 := by rw [frame3 4 (by norm_num), h4]
  have e7 : mem3 7 = 5 := by rw [frame3 7 (by norm_num), h7]
  have e8 : mem3 8 = (((2^r : ℕ)) : ℤ) := by rw [frame3 8 (by norm_num), h8]
  have e9 : mem3 9 = (((1 + 2^(r-1) : ℕ)) : ℤ) := by rw [frame3 9 (by norm_num), h9]
  have e13 : mem3 13 = ((r - 2 - i : ℕ) : ℤ) := by rw [frame3 13 (by norm_num), h13]
  have e15 : mem3 15 = ((h % 2^i : ℕ) : ℤ) := by rw [frame3 15 (by norm_num), h15]
  have e17 : mem3 17 = (((2^i : ℕ)) : ℤ) := by rw [frame3 17 (by norm_num), h17]
  have m14 : mem3 14 = mem 14 := frame3 14 (by norm_num)
  have e14 : ((mem3 14 : ℤ) : ZMod (2^r)) = (sZ r) ^ (h % 2^i) := by rw [m14, h14]
  have e16 : ((mem3 16 : ℤ) : ZMod (2^r)) = (sZ r) ^ (2^i) := by rw [frame3 16 (by norm_num), h16]
  have hbit2 : (h / 2^i) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hile' : i + 1 ≤ r - 2 := by omega
  rcases (by omega : (h / 2^i) % 2 = 0 ∨ (h / 2^i) % 2 = 1) with hc | hc
  · have hHb : Hb r h i = 1 := by rw [Hb, hc, pow_zero]
    have hy1 : mem3 19 = 1 := by
      refine eq_of_cast_eq r (mem3 19) 1 hb3.1 hb3.2 (by norm_num) ?_ ?_
      · exact_mod_cast (one_lt_two_pow (by omega : 1 ≤ r))
      · rw [hz3', hHb, Int.cast_one]
    have h193 : mem3 19 = mem3 3 := by rw [hy1, e3]
    obtain ⟨mem', hrun', f14, f15, f16, f17, f13, ffr⟩ := iter_bit0 mem3 h193
    refine ⟨(8 + 5 * (r - 3 - i)) + 7, by omega, mem', ?_, ?_⟩
    · rw [Lrun_add, hrun3, hrun']
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ffr 0 (by decide) (by decide) (by decide), e0]
      · rw [ffr 1 (by decide) (by decide) (by decide), e1]
      · rw [ffr 2 (by decide) (by decide) (by decide), e2]
      · rw [ffr 3 (by decide) (by decide) (by decide), e3]
      · rw [ffr 4 (by decide) (by decide) (by decide), e4]
      · rw [ffr 7 (by decide) (by decide) (by decide), e7]
      · rw [ffr 8 (by decide) (by decide) (by decide), e8]
      · rw [ffr 9 (by decide) (by decide) (by decide), e9]
      · rw [f13, e13, e3]; push_cast; omega
      · rw [f15, e15, bit_zero_mod h i hc]
      · rw [f17, e17, two_pow_succ_cast i]
      · rw [ffr 24 (by decide) (by decide) (by decide), h24']
      · rw [f14, m14, h14, bit_zero_mod_nat h i hc]
      · rw [f16, e8, intCast_emod r (mem3 16 * mem3 16), Int.cast_mul, ← pow_two, e16, ← pow_mul,
            show (2:ℕ)^i * 2 = 2^(i+1) by rw [pow_succ]]
      · rw [f14, m14]; exact h14b
      · rw [f16, e8]; exact ⟨Int.emod_nonneg _ (ne_of_gt hMpos), Int.emod_lt_of_pos _ hMpos⟩
      · rw [f15, e15]; exact_mod_cast Nat.zero_le _
      · rw [f17, e17]; exact_mod_cast Nat.zero_le _
      · exact hile'
  · have hHb : Hb r h i = (((1 + 2^(r-1) : ℕ)) : ZMod (2^r)) := by rw [Hb, hc, pow_one, five_pow_ord2 r hr]
    have hyH : mem3 19 = (((1 + 2^(r-1) : ℕ)) : ℤ) := by
      refine eq_of_cast_eq r (mem3 19) (((1 + 2^(r-1) : ℕ)) : ℤ) hb3.1 hb3.2 (by positivity) (H_lt_M r (by omega)) ?_
      rw [hz3', hHb, Int.cast_natCast]
    have h19H : mem3 19 = mem3 9 := by rw [hyH, e9]
    have h9ne : mem3 9 ≠ mem3 3 := by rw [e9, e3]; exact ne_of_gt (one_lt_H r (by omega))
    obtain ⟨mem', hrun', f14, f15, f16, f17, f13, ffr⟩ := iter_bit1 mem3 h19H h9ne
    refine ⟨(8 + 5 * (r - 3 - i)) + 11, by omega, mem', ?_, ?_⟩
    · rw [Lrun_add, hrun3, hrun']
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ffr 0 (by decide) (by decide) (by decide) (by decide) (by decide), e0]
      · rw [ffr 1 (by decide) (by decide) (by decide) (by decide) (by decide), e1]
      · rw [ffr 2 (by decide) (by decide) (by decide) (by decide) (by decide), e2]
      · rw [ffr 3 (by decide) (by decide) (by decide) (by decide) (by decide), e3]
      · rw [ffr 4 (by decide) (by decide) (by decide) (by decide) (by decide), e4]
      · rw [ffr 7 (by decide) (by decide) (by decide) (by decide) (by decide), e7]
      · rw [ffr 8 (by decide) (by decide) (by decide) (by decide) (by decide), e8]
      · rw [ffr 9 (by decide) (by decide) (by decide) (by decide) (by decide), e9]
      · rw [f13, e13, e3]; push_cast; omega
      · rw [f15, e15, e17, bit_one_mod h i hc]
      · rw [f17, e17, two_pow_succ_cast i]
      · rw [ffr 24 (by decide) (by decide) (by decide) (by decide) (by decide), h24']
      · rw [f14, e8, intCast_emod r (mem3 14 * mem3 16), Int.cast_mul, e14, e16, ← pow_add, bit_one_mod_nat h i hc]
      · rw [f16, e8, intCast_emod r (mem3 16 * mem3 16), Int.cast_mul, ← pow_two, e16, ← pow_mul,
            show (2:ℕ)^i * 2 = 2^(i+1) by rw [pow_succ]]
      · rw [f14, e8]; exact ⟨Int.emod_nonneg _ (ne_of_gt hMpos), Int.emod_lt_of_pos _ hMpos⟩
      · rw [f16, e8]; exact ⟨Int.emod_nonneg _ (ne_of_gt hMpos), Int.emod_lt_of_pos _ hMpos⟩
      · rw [f15, e15, e17]; omega
      · rw [f17, e17]; exact_mod_cast Nat.zero_le _
      · exact hile'

/-- The failing iteration: when `p = -5^h` and `i = r-3`, the machine jumps to `⟨48,·⟩`
keeping `mem 24 = -1`. -/
theorem loop_fail (r p h : ℕ) (hr : 3 ≤ r) (i : ℕ) (hi : i = r - 3) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ 1 * (5 : ZMod (2^r)) ^ h) :
    ∀ mem, LoopInv r p h i mem →
      ∃ t ≤ 5 * (r - 3 - i) + 20, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨48, mem'⟩ ∧ mem' 24 = -1 := by
  intro mem hL
  obtain ⟨h0, h1, h2, h3, h4, h7, h8, h9, h13, h15, h17, h24, h14, h16, h14b, h16b, h15n, h17n, hile⟩ := hL
  have hi2 : i < r - 2 := by omega
  obtain ⟨mem3, hrun3, hz3, hb3, hfr3⟩ := iter_core r 1 h i p hr hi2 mem h1 h2 h3 h8 h13 h14 hp
  have hz3' : ((mem3 19 : ℤ) : ZMod (2^r)) = - Hb r h i := by
    have hexp : (1 : ℕ) * 2^(r - 3 - i) = 1 := by rw [hi, Nat.sub_self]; norm_num
    rw [hz3, hexp, pow_one, neg_one_mul]
  have frame3 : ∀ k, k < 18 → mem3 k = mem k :=
    fun k hk => hfr3 k (by omega) (by omega) (by omega) (by omega)
  have e3 : mem3 3 = 1 := by rw [frame3 3 (by norm_num), h3]
  have hM9 : mem3 9 = (((1 + 2^(r-1) : ℕ)) : ℤ) := by rw [frame3 9 (by norm_num), h9]
  have hM24 : mem3 24 = -1 := by rw [hfr3 24 (by decide) (by decide) (by decide) (by decide), h24]
  have hne3 : mem3 19 ≠ mem3 3 := by
    intro hh'
    have h1c : ((mem3 19 : ℤ) : ZMod (2^r)) = 1 := by rw [hh', e3, Int.cast_one]
    rw [hz3'] at h1c
    rcases Hb_zero_or_one r h i hr with hb | hb
    · rw [hb] at h1c; exact neg_one_ne_one r (by omega) h1c
    · rw [hb] at h1c
      have h2c : (((1 + 2^(r-1) : ℕ)) : ZMod (2^r)) = -1 := by
        have := congrArg Neg.neg h1c; simpa using this
      exact h_ne_negone r hr h2c
  have hne9 : mem3 19 ≠ mem3 9 := by
    intro hh'
    have h1c : ((mem3 19 : ℤ) : ZMod (2^r)) = (((1 + 2^(r-1) : ℕ)) : ZMod (2^r)) := by
      rw [hh', hM9, Int.cast_natCast]
    rw [hz3'] at h1c
    rcases Hb_zero_or_one r h i hr with hb | hb
    · rw [hb] at h1c; exact h_ne_negone r hr h1c.symm
    · rw [hb] at h1c; exact neg_h_ne_h r (by omega) h1c
  obtain ⟨mem', hrun', h24'⟩ := iter_fail mem3 hne3 hne9
  refine ⟨(8 + 5 * (r - 3 - i)) + 3, by omega, mem', ?_, ?_⟩
  · rw [Lrun_add, hrun3, hrun']
  · rw [h24', hM24]


/-- Exiting the loop: at `i = r-2` the machine falls through to `⟨47,·⟩` and writes `mem 24 = h`. -/
theorem loop_exit (r p h : ℕ) (hh : h < 2^(r-2)) :
    ∀ mem, LoopInv r p h (r-2) mem → ∃ mem', Lrun 3 ⟨20, mem⟩ = ⟨47, mem'⟩ ∧ mem' 24 = (h : ℤ) := by
  intro mem hL
  obtain ⟨h0,h1,h2,h3,h4,h7,h8,h9,h13,h15,h17,h24,h14,h16,h14b,h16b,h15n,h17n,hile⟩ := hL
  have h13z : mem 13 = 0 := by rw [h13, Nat.sub_self]; norm_num
  have h15z : mem 15 = (h : ℤ) := by rw [h15, Nat.mod_eq_of_lt hh]
  have h2c : ¬ (mem 13 > mem 2) := by rw [h13z, h2]; norm_num
  have hrun : Lrun 3 ⟨20, mem⟩ = ⟨47, Function.update mem 24 (mem 15 + mem 2)⟩ := by
    rw [show (3:ℕ) = 2+1 from rfl, Lrun_succ, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst20le mem h2c, Lst21, Lst46]
  refine ⟨Function.update mem 24 (mem 15 + mem 2), hrun, ?_⟩
  rw [Function.update_self, h15z, h2]; ring

/-- The main loop, positive branch (`p = 5^h`): runs to `⟨47,·⟩` writing `h`. -/
theorem loop_pos_aux (r p h : ℕ) (hr : 3 ≤ r) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r)) ^ h) :
    ∀ k, ∀ i, r - 2 - i = k → i ≤ r - 2 → ∀ mem, LoopInv r p h i mem →
      ∃ t ≤ 5*k*k + 19*k + 3, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨47, mem'⟩ ∧ mem' 24 = (h : ℤ) := by
  intro k
  induction k with
  | zero =>
    intro i hk _ mem hL
    have hi : i = r - 2 := by omega
    rw [hi] at hL
    obtain ⟨mem', hrun, h24⟩ := loop_exit r p h hh mem hL
    exact ⟨3, by norm_num, mem', hrun, h24⟩
  | succ k ih =>
    intro i hk hile mem hL
    have hi2 : i < r - 2 := by omega
    have hp' : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ 0 * (5 : ZMod (2^r)) ^ h := by
      rw [pow_zero, one_mul]; exact hp
    have hsign : (-1 : ZMod (2^r)) ^ (0 * 2^(r-3-i)) = 1 := by rw [zero_mul, pow_zero]
    obtain ⟨t1, ht1, mem1, hrun1, hL1⟩ := loop_step r p 0 h i hr hi2 hh hp' hsign mem hL
    obtain ⟨t2, ht2, mem', hrun2, h24⟩ := ih (i+1) (by omega) (by omega) mem1 hL1
    refine ⟨t1 + t2, ?_, mem', ?_, h24⟩
    · have h1b : t1 ≤ 5*k + 20 := by omega
      have e1 : 5*(k+1)*(k+1) + 19*(k+1) + 3 = 5*k*k + 29*k + 27 := by ring
      omega
    · rw [Lrun_add, hrun1, hrun2]

/-- The main loop, negative branch (`p = -5^h`): fails at `i = r-3`, leaving `mem 24 = -1`. -/
theorem loop_neg_aux (r p h : ℕ) (hr : 3 ≤ r) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) * (5 : ZMod (2^r)) ^ h) :
    ∀ k, ∀ i, r - 3 - i = k → i ≤ r - 3 → ∀ mem, LoopInv r p h i mem →
      ∃ t ≤ 5*k*k + 30*k + 20, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨48, mem'⟩ ∧ mem' 24 = -1 := by
  intro k
  induction k with
  | zero =>
    intro i hk _ mem hL
    have hi : i = r - 3 := by omega
    have hp' : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ 1 * (5 : ZMod (2^r)) ^ h := by
      rw [pow_one]; exact hp
    obtain ⟨t, ht, mem', hrun, h24⟩ := loop_fail r p h hr i hi hh hp' mem hL
    refine ⟨t, ?_, mem', hrun, h24⟩
    omega
  | succ k ih =>
    intro i hk hile mem hL
    have hi3 : i < r - 3 := by omega
    have hp' : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ 1 * (5 : ZMod (2^r)) ^ h := by
      rw [pow_one]; exact hp
    have hsign : (-1 : ZMod (2^r)) ^ (1 * 2^(r-3-i)) = 1 := by
      exact neg_one_pow_mul_two_pow r 1 (r-3-i) (by omega)
    obtain ⟨t1, ht1, mem1, hrun1, hL1⟩ := loop_step r p 1 h i hr (by omega) hh hp' hsign mem hL
    obtain ⟨t2, ht2, mem', hrun2, h24⟩ := ih (i+1) (by omega) (by omega) mem1 hL1
    refine ⟨t1 + t2, ?_, mem', ?_, h24⟩
    · have h1b : t1 ≤ 5*k + 25 := by omega
      have e1 : 5*(k+1)*(k+1) + 30*(k+1) + 20 = 5*k*k + 40*k + 55 := by ring
      omega
    · rw [Lrun_add, hrun1, hrun2]

theorem loop_pos (r p h : ℕ) (hr : 3 ≤ r) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r)) ^ h) :
    ∀ mem, LoopInv r p h 0 mem →
      ∃ t ≤ 5*(r-2)*(r-2) + 19*(r-2) + 3, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨47, mem'⟩ ∧ mem' 24 = (h : ℤ) :=
  fun mem hL => loop_pos_aux r p h hr hh hp (r-2) 0 rfl (by omega) mem hL

theorem loop_neg (r p h : ℕ) (hr : 3 ≤ r) (hh : h < 2^(r-2))
    (hp : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) * (5 : ZMod (2^r)) ^ h) :
    ∀ mem, LoopInv r p h 0 mem →
      ∃ t ≤ 5*(r-3)*(r-3) + 30*(r-3) + 20, ∃ mem', Lrun t ⟨20, mem⟩ = ⟨48, mem'⟩ ∧ mem' 24 = -1 :=
  fun mem hL => loop_neg_aux r p h hr hh hp (r-3) 0 rfl (by omega) mem hL



/-! ## The prelude, the representation of `p`, and Lemma 1 -/

/-- The `(ZMod (2^r))ˣ`-representation `p = (-1)^j · 5^h` of an odd `p`. -/
noncomputable def pRepr (r p : ℕ) (hr : 2 ≤ r) (hodd : Odd p) : Fin 2 × Fin (2^(r-2)) :=
  Classical.choose (BkSet.reprMap_surjective r hr
    (ZMod.unitOfCoprime p (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr hodd))))

theorem pRepr_spec (r p : ℕ) (hr : 2 ≤ r) (hodd : Odd p) :
    BkSet.reprMap r (pRepr r p hr hodd)
      = ZMod.unitOfCoprime p (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr hodd)) :=
  Classical.choose_spec (BkSet.reprMap_surjective r hr
    (ZMod.unitOfCoprime p (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr hodd))))

theorem pRepr_cast (r p : ℕ) (hr : 3 ≤ r) (hodd : Odd p) :
    ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) ^ ((pRepr r p (by omega) hodd).1 : ℕ)
      * (5 : ZMod (2^r)) ^ ((pRepr r p (by omega) hodd).2 : ℕ) := by
  have h := congrArg (fun u : (ZMod (2^r))ˣ => (u : ZMod (2^r))) (pRepr_spec r p (by omega) hodd)
  simp only [BkSet.reprMap, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    BkSet.fiveUnit, ZMod.coe_unitOfCoprime] at h
  simpa using h.symm

theorem prelude_run (r p : ℕ) (hr : 3 ≤ r) :
    ∃ t ≤ 11*r + 13, ∃ mem : ℕ → ℤ, Lrun t (Ls0 r p) = ⟨20, mem⟩ ∧
      LoopInv r p 0 0 mem ∧ mem 16 = mem 10 ∧
      mem 18 = 0 ∧ mem 19 = 0 ∧ mem 20 = 0 ∧ mem 21 = 0 := by
  set I : ℕ → ℤ := LinitMem r p with hI
  have I0 : I 0 = (r:ℤ) := by simp [I, LinitMem]
  have I1 : I 1 = (p:ℤ) := by simp [I, LinitMem]
  have I2 : I 2 = 0 := by simp [I, LinitMem]
  have I3 : I 3 = 1 := by simp [I, LinitMem]
  have I4 : I 4 = 2 := by simp [I, LinitMem]
  have I5 : I 5 = 3 := by simp [I, LinitMem]
  have I6 : I 6 = 4 := by simp [I, LinitMem]
  have I7 : I 7 = 5 := by simp [I, LinitMem]
  have I14 : I 14 = 1 := by simp [I, LinitMem]
  have I15 : I 15 = 0 := by simp [I, LinitMem]
  have I17 : I 17 = 1 := by simp [I, LinitMem]
  have I24 : I 24 = -1 := by simp [I, LinitMem]
  have Ifr : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 →
      i ≠ 14 → i ≠ 17 → i ≠ 24 → I i = 0 := by
    intro i a0 a1 a2 a3 a4 a5 a6 a7 a14 a17 a24
    simp only [I, LinitMem]
    rw [if_neg a0, if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_neg a5, if_neg a6, if_neg a7,
        if_neg a14, if_neg a17, if_neg a24]
  have s1 : Lrun 1 (Ls0 r p) = ⟨1, Function.update I 8 1⟩ := by
    have h32 : I 3 + I 2 = (1:ℤ) := by rw [I3, I2, add_zero]
    rw [show (1:ℕ) = 0+1 from rfl, Lrun_succ, Lrun_zero,
        show (Ls0 r p) = (⟨0, I⟩ : State) from rfl, Lst0, h32]
  set A : ℕ → ℤ := Function.update I 8 1 with hA
  have A8 : A 8 = 1 := by rw [hA, Function.update_self]
  have Afr : ∀ i, i ≠ 8 → A i = I i := fun i hi => by rw [hA, Function.update_of_ne hi]
  have A0 : A 0 = (r:ℤ) := by rw [Afr 0 (by decide), I0]
  have A2 : A 2 = 0 := by rw [Afr 2 (by decide), I2]
  have A3 : A 3 = 1 := by rw [Afr 3 (by decide), I3]
  have s2 : Lrun 2 (Ls0 r p) = ⟨2, Function.update A 22 (r:ℤ)⟩ := by
    have h02 : A 0 + A 2 = (r:ℤ) := by rw [A0, A2, add_zero]
    rw [show (2:ℕ) = 1+1 from rfl, Lrun_succ, s1, Lst1, h02]
  set B : ℕ → ℤ := Function.update A 22 (r:ℤ) with hB
  have B22 : B 22 = (r:ℤ) := by rw [hB, Function.update_self]
  have B2 : B 2 = 0 := by rw [hB, Function.update_of_ne (by decide : (2:ℕ) ≠ 22), A2]
  have B3 : B 3 = 1 := by rw [hB, Function.update_of_ne (by decide : (3:ℕ) ≠ 22), A3]
  have B8 : B 8 = 1 := by rw [hB, Function.update_of_ne (by decide : (8:ℕ) ≠ 22), A8]
  have Bfr : ∀ i, i ≠ 22 → B i = A i := fun i hi => by rw [hB, Function.update_of_ne hi]
  obtain ⟨t1, ht1, C, hrun1, hC8, hC22, hCfr⟩ := pre_double r B B22 B2 B3
  have C8 : C 8 = (((2^r:ℕ)):ℤ) := by rw [hC8, B8]; push_cast; ring
  have Cfr : ∀ i, i ≠ 8 → i ≠ 22 → C i = I i :=
    fun i hi8 hi22 => by rw [hCfr i hi8 hi22, Bfr i hi22, Afr i hi8]
  have C0 : C 0 = (r:ℤ) := by rw [Cfr 0 (by decide) (by decide), I0]
  have C2 : C 2 = 0 := by rw [Cfr 2 (by decide) (by decide), I2]
  have C3 : C 3 = 1 := by rw [Cfr 3 (by decide) (by decide), I3]
  have C4 : C 4 = 2 := by rw [Cfr 4 (by decide) (by decide), I4]
  have C7 : C 7 = 5 := by rw [Cfr 7 (by decide) (by decide), I7]
  have hdiv : (((2^r:ℕ)):ℤ) / 2 = (((2^(r-1):ℕ)):ℤ) := by
    have h : (((2^r:ℕ)):ℤ) = 2 * (((2^(r-1):ℕ)):ℤ) := by
      push_cast; rw [mul_comm, two_mul_pow_pred_int r (by omega)]
    rw [h]; omega
  set C1 : ℕ → ℤ := Function.update C 9 (C 8 / C 4) with hC1
  set D : ℕ → ℤ := Function.update C1 9 (C1 9 + C1 3) with hD
  have s67 : Lrun 2 ⟨6, C⟩ = ⟨8, D⟩ := by
    rw [show (2:ℕ) = 1+1 from rfl, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst6, ← hC1, Lst7, ← hD]
  have D9 : D 9 = (((1 + 2^(r-1):ℕ)):ℤ) := by
    rw [hD, Function.update_self, hC1, Function.update_self,
        Function.update_of_ne (by decide : (3:ℕ) ≠ 9), C8, C4, C3, hdiv]
    push_cast; ring
  have C1fr : ∀ i, i ≠ 9 → C1 i = C i := fun i hi => by rw [hC1, Function.update_of_ne hi]
  have Dfr : ∀ i, i ≠ 9 → D i = C i := fun i hi => by rw [hD, Function.update_of_ne hi, C1fr i hi]
  have D0 : D 0 = (r:ℤ) := by rw [Dfr 0 (by decide), C0]
  have D2 : D 2 = 0 := by rw [Dfr 2 (by decide), C2]
  have D3 : D 3 = 1 := by rw [Dfr 3 (by decide), C3]
  have D4 : D 4 = 2 := by rw [Dfr 4 (by decide), C4]
  have D7 : D 7 = 5 := by rw [Dfr 7 (by decide), C7]
  have D8 : D 8 = (((2^r:ℕ)):ℤ) := by rw [Dfr 8 (by decide), C8]
  have DfrI : ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 22 → D i = I i :=
    fun i a b c => by rw [Dfr i b, Cfr i a c]
  set E1 : ℕ → ℤ := Function.update D 10 (D 3 + D 2) with hE1
  set E : ℕ → ℤ := Function.update E1 22 (E1 0 - E1 4) with hE
  have s89 : Lrun 2 ⟨8, D⟩ = ⟨10, E⟩ := by
    rw [show (2:ℕ) = 1+1 from rfl, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst8, ← hE1, Lst9, ← hE]
  have E10 : E 10 = 1 := by
    rw [hE, Function.update_of_ne (by decide : (10:ℕ) ≠ 22), hE1, Function.update_self, D3, D2]; norm_num
  have E22 : E 22 = ((r - 2 : ℕ) : ℤ) := by
    rw [hE, Function.update_self, hE1, Function.update_of_ne (by decide : (0:ℕ) ≠ 10),
        Function.update_of_ne (by decide : (4:ℕ) ≠ 10), D0, D4]
    push_cast; omega
  have E2 : E 2 = 0 := by
    rw [hE, Function.update_of_ne (by decide : (2:ℕ) ≠ 22), hE1, Function.update_of_ne (by decide : (2:ℕ) ≠ 10), D2]
  have E3 : E 3 = 1 := by
    rw [hE, Function.update_of_ne (by decide : (3:ℕ) ≠ 22), hE1, Function.update_of_ne (by decide : (3:ℕ) ≠ 10), D3]
  have E7 : E 7 = 5 := by
    rw [hE, Function.update_of_ne (by decide : (7:ℕ) ≠ 22), hE1, Function.update_of_ne (by decide : (7:ℕ) ≠ 10), D7]
  have E8 : E 8 = (((2^r:ℕ)):ℤ) := by
    rw [hE, Function.update_of_ne (by decide : (8:ℕ) ≠ 22), hE1, Function.update_of_ne (by decide : (8:ℕ) ≠ 10), D8]
  have Efr : ∀ i, i ≠ 10 → i ≠ 22 → E i = D i :=
    fun i a b => by rw [hE, Function.update_of_ne b, hE1, Function.update_of_ne a]
  have hE10n : (0:ℤ) ≤ E 10 := by rw [E10]; norm_num
  have hE10u : E 10 < (((2^r:ℕ)):ℤ) := by rw [E10]; exact_mod_cast (one_lt_two_pow (by omega : 1 ≤ r))
  obtain ⟨t2, ht2, F, hrun2, hF10z, hF10n, hF10u, hFfr⟩ :=
    pre_inv r (r-2) (by omega) E E22 E2 E3 E7 E8 hE10n hE10u
  have F2 : F 2 = 0 := by rw [hFfr 2 (by decide) (by decide), E2]
  have F10z : ((F 10 : ℤ) : ZMod (2^r)) = sZ r := by
    rw [hF10z, E10, Int.cast_one, one_pow, one_mul, sZ]
  set F1 : ℕ → ℤ := Function.update F 16 (F 10 + F 2) with hF1
  set G : ℕ → ℤ := Function.update F1 13 (F1 0 - F1 4) with hG
  have run17 : Lrun 2 ⟨17, F⟩ = ⟨19, G⟩ := by
    rw [show (2:ℕ) = 1+1 from rfl, Lrun_succ, Lrun_succ, Lrun_zero]
    rw [Lst17, ← hF1, Lst18, ← hG]
  have run19 : Lrun 1 ⟨19, G⟩ = ⟨20, G⟩ := by
    rw [show (1:ℕ) = 0+1 from rfl, Lrun_succ, Lrun_zero]; rw [Lst19]
  have r1 : Lrun (2 + t1) (Ls0 r p) = ⟨6, C⟩ := by rw [Lrun_add, s2, hrun1]
  have r2 : Lrun (2 + t1 + 2) (Ls0 r p) = ⟨8, D⟩ := by rw [Lrun_add, r1, s67]
  have r3 : Lrun (2 + t1 + 2 + 2) (Ls0 r p) = ⟨10, E⟩ := by rw [Lrun_add, r2, s89]
  have r4 : Lrun (2 + t1 + 2 + 2 + t2) (Ls0 r p) = ⟨17, F⟩ := by rw [Lrun_add, r3, hrun2]
  have r5 : Lrun (2 + t1 + 2 + 2 + t2 + 2) (Ls0 r p) = ⟨19, G⟩ := by rw [Lrun_add, r4, run17]
  have r6 : Lrun (2 + t1 + 2 + 2 + t2 + 2 + 1) (Ls0 r p) = ⟨20, G⟩ := by rw [Lrun_add, r5, run19]
  have F1fr : ∀ i, i ≠ 16 → F1 i = F i := fun i hi => by rw [hF1, Function.update_of_ne hi]
  have Gfr : ∀ i, i ≠ 13 → i ≠ 16 → i ≠ 10 → i ≠ 22 → i ≠ 8 → i ≠ 9 → G i = I i := by
    intro i a13 a16 a10 a22 a8 a9
    rw [hG, Function.update_of_ne a13, F1fr i a16,
        hFfr i a10 a22, Efr i a10 a22, DfrI i a8 a9 a22]
  have G0 : G 0 = (r:ℤ) := by rw [Gfr 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I0]
  have G1 : G 1 = (p:ℤ) := by rw [Gfr 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I1]
  have G2 : G 2 = 0 := by rw [Gfr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I2]
  have G3 : G 3 = 1 := by rw [Gfr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I3]
  have G4 : G 4 = 2 := by rw [Gfr 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I4]
  have G7 : G 7 = 5 := by rw [Gfr 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I7]
  have G8 : G 8 = (((2^r:ℕ)):ℤ) := by
    rw [hG, Function.update_of_ne (by decide : (8:ℕ) ≠ 13), F1fr 8 (by decide),
        hFfr 8 (by decide) (by decide), Efr 8 (by decide) (by decide), D8]
  have G9 : G 9 = (((1 + 2^(r-1):ℕ)):ℤ) := by
    rw [hG, Function.update_of_ne (by decide : (9:ℕ) ≠ 13), F1fr 9 (by decide),
        hFfr 9 (by decide) (by decide), Efr 9 (by decide) (by decide), D9]
  have G13 : G 13 = ((r - 2 : ℕ) : ℤ) := by
    rw [hG, Function.update_self, F1fr 0 (by decide), F1fr 4 (by decide),
        hFfr 0 (by decide) (by decide), hFfr 4 (by decide) (by decide),
        Efr 0 (by decide) (by decide), Efr 4 (by decide) (by decide),
        DfrI 0 (by decide) (by decide) (by decide), DfrI 4 (by decide) (by decide) (by decide), I0, I4]
    omega
  have G14 : G 14 = 1 := by rw [Gfr 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I14]
  have G15 : G 15 = 0 := by rw [Gfr 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I15]
  have G17 : G 17 = 1 := by rw [Gfr 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I17]
  have G24 : G 24 = -1 := by rw [Gfr 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I24]
  have G18 : G 18 = 0 := by
    rw [Gfr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        Ifr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have G19 : G 19 = 0 := by
    rw [Gfr 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        Ifr 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have G20 : G 20 = 0 := by
    rw [Gfr 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        Ifr 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have G21 : G 21 = 0 := by
    rw [Gfr 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        Ifr 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have G16 : G 16 = F 10 := by
    rw [hG, Function.update_of_ne (by decide : (16:ℕ) ≠ 13), hF1, Function.update_self, F2, add_zero]
  have G10 : G 10 = F 10 := by rw [hG, Function.update_of_ne (by decide : (10:ℕ) ≠ 13), F1fr 10 (by decide)]
  have G16z : ((G 16 : ℤ) : ZMod (2^r)) = sZ r := by rw [G16, F10z]
  have G16b : (0:ℤ) ≤ G 16 ∧ G 16 < (((2^r:ℕ)):ℤ) := by rw [G16]; exact ⟨hF10n, hF10u⟩
  have G14b : (0:ℤ) ≤ G 14 ∧ G 14 < (((2^r:ℕ)):ℤ) := by
    rw [G14]; refine ⟨by norm_num, ?_⟩; exact_mod_cast (one_lt_two_pow (by omega : 1 ≤ r))
  refine ⟨t1 + t2 + 9, ?_, G, ?_, ?_, ?_, G18, G19, G20, G21⟩
  · omega
  · rw [show t1 + t2 + 9 = 2 + t1 + 2 + 2 + t2 + 2 + 1 by omega, r6]
  · refine ⟨G0, G1, G2, G3, G4, G7, G8, G9, G13, ?_, ?_, G24, ?_, ?_, G14b, G16b, ?_, ?_, ?_⟩
    · rw [G15]; norm_num
    · rw [G17]; norm_num
    · rw [G14]; norm_num
    · rw [G16z, pow_zero, pow_one]
    · rw [G15]
    · rw [G17]; norm_num
    · omega
  · rw [G16, G10]


/-- The discrete-logarithm machine.  For odd `p` with `1 ≤ p < 2^r`
the program `Lprog` halts in `O(r^2)` steps; it returns `ind_5 p` (as an integer in `mem 24`)
when `p ∈ ⟨5⟩`, and `-1` otherwise (`st.pc = 47` on success, `48` on failure). -/
theorem lemma1 (r p : ℕ) (hr : 3 ≤ r) (hodd : Odd p) (hp1 : 1 ≤ p) (hpu : p < 2^r) :
    ∃ T ≤ 40*(r+1)*(r+1) + 100, ∃ st : State, Lrun T (Ls0 r p) = st ∧
      ((st.pc = 47 ∧ ∃ a : ℕ, a < 2^(r-2) ∧ ((p : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r))^a
          ∧ st.mem 24 = (a : ℤ))
       ∨ (st.pc = 48 ∧ st.mem 24 = -1 ∧
          ∀ a : ℕ, a < 2^(r-2) → ((p : ℤ) : ZMod (2^r)) ≠ (5 : ZMod (2^r))^a)) := by
  obtain ⟨t0, ht0, mem0, hrun0, hL0, h1610, h180, h190, h200, h210⟩ := prelude_run r p hr
  obtain ⟨j, hh, hjeq⟩ : ∃ (j : Fin 2) (hh : Fin (2^(r-2))),
      pRepr r p (by omega) hodd = (j, hh) :=
    ⟨(pRepr r p (by omega) hodd).1, (pRepr r p (by omega) hodd).2, rfl⟩
  have hpj' : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r))^(j:ℕ) * (5 : ZMod (2^r))^(hh:ℕ) := by
    have h1 : ((pRepr r p (by omega) hodd).1 : ℕ) = (j:ℕ) := by rw [congrArg Prod.fst hjeq]
    have h2 : ((pRepr r p (by omega) hodd).2 : ℕ) = (hh:ℕ) := by rw [congrArg Prod.snd hjeq]
    rw [pRepr_cast r p hr hodd, h1, h2]
  have hhlt : (hh : ℕ) < 2^(r-2) := hh.isLt
  have hjlt : (j : ℕ) < 2 := j.isLt
  have hL0' : LoopInv r p (hh : ℕ) 0 mem0 := by
    simpa only [LoopInv, pow_zero, Nat.mod_one] using hL0
  rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hj | hj
  · have hp0 : ((p : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r))^(hh : ℕ) := by
      rw [hpj', hj, pow_zero, one_mul]
    obtain ⟨t1, ht1, mem1, hrun1, h24⟩ := loop_pos r p (hh : ℕ) hr hhlt hp0 mem0 hL0'
    refine ⟨t0 + t1, ?_, (⟨47, mem1⟩ : State), ?_, Or.inl ⟨rfl, (hh:ℕ), hhlt, hp0, h24⟩⟩
    · have h0b : t0 ≤ 11*(r-2) + 35 := by omega
      nlinarith [Nat.sub_le r 2, Nat.zero_le (r-2)]
    · rw [Lrun_add, hrun0, hrun1]
  · have hp1' : ((p : ℤ) : ZMod (2^r)) = (-1 : ZMod (2^r)) * (5 : ZMod (2^r))^(hh : ℕ) := by
      rw [hpj', hj, pow_one]
    obtain ⟨t1, ht1, mem1, hrun1, h24⟩ := loop_neg r p (hh : ℕ) hr hhlt hp1' mem0 hL0'
    have hne : ∀ a, a < 2^(r-2) → ((p : ℤ) : ZMod (2^r)) ≠ (5 : ZMod (2^r))^a := by
      intro a ha heq
      have hc : Nat.Coprime p (2^r) := Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr hodd)
      have heq' : (p : ZMod (2^r)) = (5 : ZMod (2^r))^a := by simpa using heq
      have hunit : (ZMod.unitOfCoprime p hc) = (BkSet.fiveUnit r)^a := by
        apply Units.ext
        rw [ZMod.coe_unitOfCoprime, BkSet.fiveUnit, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
        simpa using heq'
      have hrepr : BkSet.reprMap r (pRepr r p (by omega) hodd) = BkSet.reprMap r (0, ⟨a, ha⟩) := by
        rw [pRepr_spec, hunit, BkSet.reprMap]; simp
      have hj0 : (j : ℕ) = 0 := by
        have h1 := congrArg Prod.fst (BkSet.reprMap_injective r (by omega : 2 ≤ r) hrepr)
        have hfj : j = (pRepr r p (by omega) hodd).1 := (congrArg Prod.fst hjeq).symm
        have h2 : j = (0 : Fin 2) := by rw [hfj, h1]
        rw [h2]; rfl
      omega
    refine ⟨t0 + t1, ?_, (⟨48, mem1⟩ : State), ?_, Or.inr ⟨rfl, h24, hne⟩⟩
    · have h0b : t0 ≤ 11*(r-2) + 35 := by omega
      nlinarith [Nat.sub_le r 2, Nat.sub_le r 3, Nat.zero_le (r-3)]
    · rw [Lrun_add, hrun0, hrun1]
structure AInv (r pc : ℕ) (mem : ℕ → ℤ) : Prop where
  nnp : ∀ i, i ≠ 24 → 0 ≤ mem i
  m24 : -1 ≤ mem 24
  univ : ∀ i, mem i ≤ (2:ℤ)^(2*r)
  r0 : mem 0 = (r:ℤ)
  c2 : mem 2 = 0
  c3 : mem 3 = 1
  c4 : mem 4 = 2
  c7 : mem 7 = 5
  r1 : mem 1 ≤ (2:ℤ)^r
  r8 : mem 8 ≤ (2:ℤ)^r
  r8one : pc = 1 → mem 8 = 1
  r8pos : 6 ≤ pc → (0:ℤ) < mem 8
  r9 : mem 9 ≤ (2:ℤ)^r + 1
  t9 : pc = 7 → mem 9 ≤ (2:ℤ)^r
  r13 : mem 13 ≤ (2:ℤ)^r
  r15 : mem 15 ≤ (2:ℤ)^r
  r17 : mem 17 ≤ (2:ℤ)^r
  r20 : mem 20 ≤ (2:ℤ)^r
  r21 : mem 21 ≤ (2:ℤ)^r
  r22 : mem 22 ≤ (2:ℤ)^r
  r24 : mem 24 ≤ (2:ℤ)^r
  r22nn : 0 ≤ mem 22
  n10 : pc ≠ 12 → pc ≠ 14 → mem 10 ≤ (2:ℤ)^r
  n14 : pc ≠ 38 → mem 14 ≤ (2:ℤ)^r
  n16 : pc ≠ 42 → mem 16 ≤ (2:ℤ)^r
  n18 : pc ≠ 23 → mem 18 ≤ (2:ℤ)^r
  n19 : pc ≠ 30 → mem 19 ≤ (2:ℤ)^r
  t8 : pc = 3 → mem 8 ≤ (2:ℤ)^(r-1)
  t13 : 22 ≤ pc → pc ≤ 44 → 1 ≤ mem 13
  sqn : 19 ≤ pc → pc ≤ 45 → pc ≠ 25 → pc ≠ 26 → mem 21 ≤ mem 20
  t2120 : 29 ≤ pc → pc ≤ 31 → mem 21 < mem 20
  a1 : (20 ≤ pc ∧ pc ≤ 36) ∨ (44 ≤ pc ∧ pc ≤ 45) → mem 15 ≤ mem 17
  a2 : 37 ≤ pc → pc ≤ 43 → mem 15 ≤ 2 * mem 17
  dbl : 2 ≤ pc → pc ≤ 5 → mem 8 * (2:ℤ) ^ (mem 22).toNat = (2:ℤ)^(r + (if pc = 4 then 1 else 0))
  g22a : 3 ≤ pc → pc ≤ 4 → 1 ≤ mem 22
  g22b : 11 ≤ pc → pc ≤ 15 → 1 ≤ mem 22
  bit : 19 ≤ pc → pc ≤ 45 → mem 17 * (2:ℤ) ^ (mem 13).toNat = (2:ℤ)^(r-2 + (if pc = 44 then 1 else 0))
  boot : pc ≤ 19 → mem 17 = 1 ∧ mem 15 = 0 ∧ mem 20 = 0 ∧ mem 21 = 0


lemma le_of_mul_pow_eq {x : ℤ} {k r : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hx : x * (2:ℤ)^k = (2:ℤ)^r) : x ≤ (2:ℤ)^(r-1) := by
  have hkpos : (0:ℤ) < (2:ℤ)^k := by positivity
  have hrpos : (0:ℤ) < (2:ℤ)^r := by positivity
  have hxpos : 0 < x := by
    by_contra hle
    have hle' : x ≤ 0 := by omega
    have h1 : x * (2:ℤ)^k ≤ 0 * (2:ℤ)^k := mul_le_mul_of_nonneg_right hle' (le_of_lt hkpos)
    rw [hx, zero_mul] at h1
    linarith [hrpos]
  have hk2 : (2:ℤ)^k = (2:ℤ)^(k-1) * 2 := by
    conv_lhs => rw [show k = (k-1)+1 by omega, pow_succ]
  have hr2 : (2:ℤ)^r = (2:ℤ)^(r-1) * 2 := by
    conv_lhs => rw [show r = (r-1)+1 by omega, pow_succ]
  have hk1 : (1:ℤ) ≤ (2:ℤ)^(k-1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (by omega : 0 ≤ k-1)
    simpa using h
  have hxy : x * (2:ℤ)^(k-1) = (2:ℤ)^(r-1) := by
    have h := hx
    rw [hk2, hr2] at h
    linarith
  nlinarith [hxy, hk1, hxpos]

lemma le_of_mul_pow_eq' {x : ℤ} {k r : ℕ} (hx0 : 0 ≤ x)
    (hx : x * (2:ℤ)^k = (2:ℤ)^r) : x ≤ (2:ℤ)^r := by
  have hk1 : (1:ℤ) ≤ (2:ℤ)^k := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (Nat.zero_le k)
    simpa using h
  nlinarith [hx, hk1, hx0]

lemma dbl_step {x : ℤ} {k m : ℕ} (hk : 1 ≤ k) (h : x * (2:ℤ)^k = (2:ℤ)^(m+1)) :
    x * (2:ℤ)^(k-1) = (2:ℤ)^m := by
  have hk' : (2:ℤ)^k = (2:ℤ)^(k-1) * 2 := by
    conv_lhs => rw [show k = (k-1)+1 by omega, pow_succ]
  have hm' : (2:ℤ)^(m+1) = (2:ℤ)^m * 2 := by rw [pow_succ]
  rw [hk', hm'] at h
  linarith

lemma one_le_two_pow_int (k : ℕ) : (1:ℤ) ≤ (2:ℤ)^k := one_le_pow₀ (by norm_num)

lemma r_le_two_pow_int (r : ℕ) : (r:ℤ) ≤ (2:ℤ)^r := by
  have h1 : r ≤ 2^r := Nat.le_of_lt (Nat.lt_two_pow_self (n := r))
  exact_mod_cast h1

lemma r_le_two_pow_two_r (r : ℕ) : (r:ℤ) ≤ (2:ℤ)^(2*r) := by
  have h1 := r_le_two_pow_int r
  have h2 : (2:ℤ)^r ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma five_le_two_pow_two_r (r : ℕ) (hr : 3 ≤ r) : (5:ℤ) ≤ (2:ℤ)^(2*r) := by
  have h1 : (5:ℤ) ≤ (2:ℤ)^6 := by norm_num
  have h2 : (2:ℤ)^6 ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma five_le_two_pow_r (r : ℕ) (hr : 3 ≤ r) : (5:ℤ) ≤ (2:ℤ)^r := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (by omega : 3 ≤ r)
  norm_num at h; linarith

lemma M_le_B (r : ℕ) : (2:ℤ)^r ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma two_pow_sq (r : ℕ) : (2:ℤ)^r * (2:ℤ)^r = (2:ℤ)^(2*r) := by
  rw [← pow_add]; congr 1; omega

lemma two_pow_pos_int (k : ℕ) : (0:ℤ) < (2:ℤ)^k := by positivity

lemma two_pow_r_add_one_le (r : ℕ) (hr : 3 ≤ r) : (2:ℤ)^r + 1 ≤ (2:ℤ)^(2*r) := by
  have h1 : (1:ℤ) ≤ (2:ℤ)^r := one_le_two_pow_int r
  have h2 : (2:ℤ)^r + 1 ≤ (2:ℤ)^r * 2 := by linarith
  have h3 : (2:ℤ)^r * 2 = (2:ℤ)^(r+1) := by rw [pow_succ]
  have h4 : (2:ℤ)^(r+1) ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega : r+1 ≤ 2*r)
  linarith

theorem ainv_init (r p : ℕ) (hr : 3 ≤ r) (hp1 : 1 ≤ p) (hpu : p < 2^r) :
    AInv r 0 (LinitMem r p) := by
  have hpB : (p:ℤ) ≤ (2:ℤ)^(2*r) := by
    have h1 : (p:ℤ) < (2:ℤ)^(r) := by exact_mod_cast hpu
    have h2 : (2:ℤ)^(r) ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hrB : (r:ℤ) ≤ (2:ℤ)^(2*r) := by
    have h1 : r ≤ 2^r := Nat.le_of_lt (Nat.lt_two_pow_self (n := r))
    have h3 : (r:ℤ) ≤ (2:ℤ)^r := by exact_mod_cast h1
    have h2 : (2:ℤ)^(r) ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h5B : (5:ℤ) ≤ (2:ℤ)^(2*r) := by
    have h1 : (5:ℤ) ≤ (2:ℤ)^6 := by norm_num
    have h2 : (2:ℤ)^6 ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h2r : (1:ℤ) ≤ (2:ℤ)^r := one_le_two_pow_int r
  have hpM : (p:ℤ) ≤ (2:ℤ)^r := le_of_lt (by exact_mod_cast hpu)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro i hi; simp only [LinitMem]; split_ifs <;> omega
  · have h : (LinitMem r p) 24 = (-1:ℤ) := by simp only [LinitMem]; norm_num
    exact le_of_eq h.symm
  · intro i; simp only [LinitMem]; split_ifs <;> linarith [hpB, hrB, h5B]
  · simp only [LinitMem]; norm_num
  · simp only [LinitMem]; norm_num
  · simp only [LinitMem]; norm_num
  · simp only [LinitMem]; norm_num
  · simp only [LinitMem]; norm_num
  · exact hpM
  · have h : (LinitMem r p) 8 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · intro h; omega
  · intro h; omega
  · have h : (LinitMem r p) 9 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; linarith [h2r]
  · intro h; omega
  · have h : (LinitMem r p) 13 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · have h : (LinitMem r p) 15 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · have h : (LinitMem r p) 17 = (1:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; exact h2r
  · have h : (LinitMem r p) 20 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · have h : (LinitMem r p) 21 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · have h : (LinitMem r p) 22 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · have h : (LinitMem r p) 24 = (-1:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; have := pow_pos (by norm_num : (0:ℤ) < 2) r; linarith
  · have h : (LinitMem r p) 22 = (0:ℤ) := by simp only [LinitMem]; norm_num
    exact le_of_eq h.symm
  · intro h1 h2; have h : (LinitMem r p) 10 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · intro h1; have h : (LinitMem r p) 14 = (1:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; exact h2r
  · intro h1; have h : (LinitMem r p) 16 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · intro h1; have h : (LinitMem r p) 18 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · intro h1; have h : (LinitMem r p) 19 = (0:ℤ) := by simp only [LinitMem]; norm_num
    rw [h]; positivity
  · intro h; omega
  · intro h1 h2; omega
  · intro h1 h2 h3 h4; omega
  · intro h1 h2; omega
  · intro h; rcases h with h | h <;> omega
  · intro h1 h2; omega
  · intro h1 h2; omega
  · intro h1 h2; omega
  · intro h1 h2; omega
  · intro h1 h2; omega
  · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [LinitMem]; norm_num)

theorem ainv_step (r : ℕ) (hr : 3 ≤ r) (pc0 : ℕ) (mem0 : ℕ → ℤ) (pc : ℕ) (mem : ℕ → ℤ)
    (h0 : AInv r pc0 mem0) (h : Lstep ⟨pc0, mem0⟩ = ⟨pc, mem⟩) : AInv r pc mem := by
  have h0all : AInv r pc0 mem0 := h0
  obtain ⟨hnnp, hm24, huniv, hr0, hc2, hc3, hc4, hc7, hr1, hr8, hr8one, hr8pos, hr9, ht9,
      hr13, hr15, hr17, hr20, hr21, hr22, hr24, hr22nn, hn10, hn14, hn16, hn18, hn19, ht8,
      ht13, hsqn, ht2120, ha1, ha2, hdbl, hg22a, hg22b, hbit, hboot⟩ := h0
  rcases Nat.lt_or_ge pc0 49 with hp | hp
  · interval_cases pc0
    · -- pc0 = 0
      rw [Lst0 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3, hc2]; norm_num) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 8)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3, hc2]; exact one_le_two_pow_int (2*r)) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 8)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 8)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 8)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 8)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 8)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 8)]; exact hr1
      · rw [Function.update_self, hc3, hc2]; exact one_le_two_pow_int r
      · rw [Function.update_self, hc3, hc2]; norm_num
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 8)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 8)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 8)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 8)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 8)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 8)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 8)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 8)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 8)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 8)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 8)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 8)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 8)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 8)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 8)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 8)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 1
      rw [Lst1 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc2]; omega) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc2]; exact r_le_two_pow_two_r r) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 22)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 22)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 22)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 22)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 22)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 22)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8
      · intro h1; omega
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 22)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 22)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact hr21
      · rw [Function.update_self, hr0, hc2, add_zero]; exact r_le_two_pow_int r
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hr24
      · rw [Function.update_self, hr0, hc2, add_zero]; positivity
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 22)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 22)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 22)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 22)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 22)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22), Function.update_self, hr0, hc2, add_zero, hr8one rfl]; simp
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 2
      by_cases hc : mem0 22 = mem0 2
      · rw [Lst2eq mem0 hc] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro h; have hd := hdbl (by omega) (by omega); rw [hc, hc2] at hd; simp at hd; rw [hd]; positivity
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2 h3 h4; omega
        · intro h1 h2; omega
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro _; exact hboot (by omega)
      · rw [Lst2ne mem0 hc] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro h1; omega
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro _; have hd : mem0 8 * (2:ℤ)^((mem0 22).toNat) = (2:ℤ)^r := (by simpa using hdbl (by omega) (by omega)); have hne : mem0 22 ≠ 0 := (by intro h; rw [h] at hc; exact hc hc2.symm); have hk : 1 ≤ (mem0 22).toNat := (by omega); exact le_of_mul_pow_eq (by omega) hk hd
        · intro h1 h2; omega
        · intro h1 h2 h3 h4; omega
        · intro h1 h2; omega
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hdbl (by omega) (by omega)
        · intro h1 h2; have hne : mem0 22 ≠ 0 := (by intro h; rw [h] at hc; exact hc hc2.symm); omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro _; exact hboot (by omega)
    · -- pc0 = 3
      rw [Lst3 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have := hnnp 8 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 8)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h1 := ht8 rfl; have h2 : (2:ℤ)^(r-1) * 2 = (2:ℤ)^r := two_mul_pow_pred_int r (by omega); have h3 := M_le_B r; have h4 : (2:ℤ)^(r-1) ≤ (2:ℤ)^r := pow_le_pow_right₀ (by norm_num) (by omega); linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 8)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 8)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 8)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 8)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 8)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 8)]; exact hr1
      · rw [Function.update_self]; have h1 := ht8 rfl; have h2 : (2:ℤ)^(r-1) * 2 = (2:ℤ)^r := two_mul_pow_pred_int r (by omega); linarith
      · intro h1; omega
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 8)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 8)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 8)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 8)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 8)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 8)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 8)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 8)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 8)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 8)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 8)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 8)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; have hd : mem0 8 * (2:ℤ)^((mem0 22).toNat) = (2:ℤ)^r := (by simpa using hdbl (by omega) (by omega)); rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8), Function.update_self]; show (mem0 8 + mem0 8) * (2:ℤ)^((mem0 22).toNat) = (2:ℤ)^(r+1); rw [pow_succ]; nlinarith [hd]
      · intro h1 h2; rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 8)]; exact hg22a (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 8)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 8)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 8)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 8)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 4
      rw [Lst4 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hg22a (by omega) (by omega); rw [hc3]; linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := huniv 22; rw [hc3]; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 22)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 22)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 22)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 22)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 22)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 22)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8
      · intro h1; omega
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 22)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 22)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact hr21
      · rw [Function.update_self, hc3]; linarith [hr22]
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hr24
      · rw [Function.update_self, hc3]; linarith [hg22a (by omega) (by omega)]
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 22)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 22)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 22)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 22)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 22)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; have hd : mem0 8 * (2:ℤ)^((mem0 22).toNat) = (2:ℤ)^(r+1) := (by simpa using hdbl (by omega) (by omega)); have hto : (mem0 22 - 1).toNat = (mem0 22).toNat - 1 := (by have := hg22a (by omega) (by omega); omega); rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22), Function.update_self, hc3, hto]; exact dbl_step (by omega) hd
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 5
      rw [Lst5 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro h1; omega
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hdbl (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; exact hboot (by omega)
    · -- pc0 = 6
      rw [Lst6 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc4]; have := hnnp 8 (by decide); exact Int.ediv_nonneg this (by norm_num)) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 9)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc4]; have h := Int.ediv_le_self (2:ℤ) (hnnp 8 (by decide)); have := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 9)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 9)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 9)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 9)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 9)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 9)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 9)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 9)]; exact hr8pos (by omega)
      · rw [Function.update_self, hc4]; have h := Int.ediv_le_self (2:ℤ) (hnnp 8 (by decide)); linarith [hr8]
      · intro _; rw [Function.update_self, hc4]; have h := Int.ediv_le_self (2:ℤ) (hnnp 8 (by decide)); linarith [hr8]
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 9)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 9)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 9)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 9)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 9)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 9)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 9)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 9)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 9)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 9)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 9)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 9)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 9)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 9)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 9)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 9)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 9)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 7
      rw [Lst7 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have := hnnp 9 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 9)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have := ht9 rfl; have := two_pow_r_add_one_le r hr; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 9)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 9)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 9)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 9)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 9)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 9)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 9)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 9)]; exact hr8pos (by omega)
      · rw [Function.update_self, hc3]; linarith [ht9 rfl]
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 9)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 9)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 9)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 9)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 9)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 9)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 9)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 9)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 9)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 9)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 9)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 9)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 9)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 9)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 9)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 9)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 9)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 8
      rw [Lst8 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3, hc2]; norm_num) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3, hc2]; exact one_le_two_pow_int (2*r)) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 10)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 10)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 10)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 10)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 10)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22nn
      · intro h1 h2; rw [Function.update_self, hc3, hc2]; exact one_le_two_pow_int r
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 10)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 10)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 10)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 9
      rw [Lst9 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc4]; omega) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc4]; have := r_le_two_pow_two_r r; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 22)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 22)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 22)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 22)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 22)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 22)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 22)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 22)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact hr21
      · rw [Function.update_self, hr0, hc4]; have := r_le_two_pow_int r; omega
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hr24
      · rw [Function.update_self, hr0, hc4]; omega
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 22)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 22)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 22)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 22)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 22)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 10
      by_cases he : mem0 22 = mem0 2
      · rw [Lst10eq mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2 h3 h4; omega
        · intro h1 h2; omega
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro _; exact hboot (by omega)
      · rw [Lst10ne mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2 h3 h4; omega
        · intro h1 h2; omega
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; have hne : mem0 22 ≠ 0 := (by intro h; rw [h] at he; exact he hc2.symm); omega
        · intro h1 h2; omega
        · intro _; exact hboot (by omega)
    · -- pc0 = 11
      rw [Lst11 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have := hnnp 10 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hn10 (by omega) (by omega); have h0 := hnnp 10 (by decide); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 10)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 10)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 10)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 10)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 10)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22nn
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 10)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 10)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 10)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hg22b (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 12
      rw [Lst12 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 10) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 10) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 10)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 10)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 10)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 10)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 10)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22nn
      · intro h1 h2; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 10) h8; linarith [hr8]
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 10)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 10)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 10)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hg22b (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 13
      rw [Lst13 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc7]; have := hnnp 10 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hn10 (by omega) (by omega); have h0 := hnnp 10 (by decide); have h5 := five_le_two_pow_r r (by omega); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 10)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 10)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 10)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 10)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 10)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22nn
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 10)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 10)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 10)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hg22b (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 14
      rw [Lst14 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 10) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 10) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 10)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 10)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 10)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 10)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 10)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 10)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 10)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 10)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 10)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 10)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hr22nn
      · intro h1 h2; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 10) h8; linarith [hr8]
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 10)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 10)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 10)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 10)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 10)]; exact hg22b (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 10)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 10)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 10)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 15
      rw [Lst15 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hg22b (by omega) (by omega); rw [hc3]; linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := huniv 22; rw [hc3]; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 22)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 22)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 22)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 22)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 22)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 22)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 22)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 22)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 22)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact hr21
      · rw [Function.update_self, hc3]; linarith [hr22]
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 22)]; exact hr24
      · rw [Function.update_self, hc3]; linarith [hg22b (by omega) (by omega)]
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 22)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 22)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 22)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 22)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 22)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 22)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 22)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 22)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 16
      rw [Lst16 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; exact hboot (by omega)
    · -- pc0 = 17
      rw [Lst17 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2]; have := hnnp 10 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2, add_zero]; have := huniv 10; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 16)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 16)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 16)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 16)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 16)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 16)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 16)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 16)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 16)]; exact hn14 (by omega)
      · intro h1; rw [Function.update_self, hc2, add_zero]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 16)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 16)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 18
      rw [Lst18 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc4]; omega) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 13)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hr0, hc4]; have := r_le_two_pow_two_r r; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 13)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 13)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 13)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 13)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 13)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 13)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 13)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 13)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 13)]; exact hr9
      · intro h1; omega
      · rw [Function.update_self, hr0, hc4]; have := r_le_two_pow_int r; omega
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 13)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 13)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 13)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 13)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 13)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 13)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 13)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 13)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 13)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; have hb := hboot (by omega); rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 13), Function.update_of_ne (by decide : (20:ℕ) ≠ 13)]; exact le_of_eq ((hb.2.2.2).trans (hb.2.2.1).symm)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; have hb := (hboot (by omega)).1; have ht : (((r:ℤ) - 2)).toNat = r - 2 := (by omega); rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 13), Function.update_self, hr0, hc4, hb]; simp only [one_mul]; rw [ht]; simp
      · intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 13)]; exact (hboot (by omega)).1) | (rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13)]; exact (hboot (by omega)).2.1) | (rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 13)]; exact (hboot (by omega)).2.2.1) | (rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 13)]; exact (hboot (by omega)).2.2.2)
    · -- pc0 = 19
      rw [Lst19 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; have hb := hboot (by omega); rw [hb.2.1, hb.1]; norm_num
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 20
      by_cases hgt : mem0 13 > mem0 2
      · rw [Lst20gt mem0 hgt] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; have h := hgt; rw [hc2] at h; omega
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
      · rw [Lst20le mem0 hgt] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; omega
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
    · -- pc0 = 21
      rw [Lst21 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1; omega
    · -- pc0 = 22
      rw [Lst22 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h14 := hnnp 14 (by decide); have h1 := hnnp 1 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 18)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h14 := hn14 (by omega); have h1 := hr1; have h014 := hnnp 14 (by decide); have h01 := hnnp 1 (by decide); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 18)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 18)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 18)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 18)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 18)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 18)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 18)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 18)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 18)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 18)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 18)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 18)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 18)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 18)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 18)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 18)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 18)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 18)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 18)]; exact hn16 (by omega)
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 18)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 18), Function.update_of_ne (by decide : (20:ℕ) ≠ 18)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 18), Function.update_of_ne (by decide : (17:ℕ) ≠ 18)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 18), Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 23
      rw [Lst23 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 18) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 18)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 18) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 18)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 18)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 18)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 18)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 18)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 18)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 18)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 18)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 18)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 18)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 18)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 18)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 18)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 18)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 18)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 18)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 18)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 18)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 18)]; exact hn16 (by omega)
      · intro h1; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 18) h8; linarith [hr8]
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 18)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 18), Function.update_of_ne (by decide : (20:ℕ) ≠ 18)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 18), Function.update_of_ne (by decide : (17:ℕ) ≠ 18)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 18), Function.update_of_ne (by decide : (13:ℕ) ≠ 18)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 24
      rw [Lst24 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := ht13 (by omega) (by omega); rw [hc3]; linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 20)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have := huniv 13; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 20)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 20)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 20)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 20)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 20)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 20)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 20)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 20)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 20)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 20)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 20)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 20)]; exact hr17
      · rw [Function.update_self, hc3]; linarith [hr13]
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 20)]; exact le_trans (hsqn (by omega) (by omega) (by omega) (by omega)) hr20
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 20)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 20)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 20)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 20)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 20)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 20)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 20)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 20)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 20)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 20), Function.update_of_ne (by decide : (17:ℕ) ≠ 20)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 20), Function.update_of_ne (by decide : (13:ℕ) ≠ 20)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 25
      rw [Lst25 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2]; have := hnnp 18 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2, add_zero]; have := huniv 18; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 19)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 19)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 19)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 19)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 19)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 19)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 19)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 19)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 19)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 19)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 19)]; exact hn18 (by omega)
      · intro h1; rw [Function.update_self, hc2, add_zero]; exact hn18 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19), Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19), Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 26
      rw [Lst26 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2]; norm_num) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 21)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2, add_zero]; positivity) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 21)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 21)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 21)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 21)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 21)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 21)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 21)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 21)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 21)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 21)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 21)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 21)]; exact hr20
      · rw [Function.update_self, hc2, add_zero]; positivity
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 21)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 21)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 21)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 21)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 21)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 21)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 21)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 21)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_self, Function.update_of_ne (by decide : (20:ℕ) ≠ 21), hc2, add_zero]; exact hnnp 20 (by decide)
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 21), Function.update_of_ne (by decide : (17:ℕ) ≠ 21)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 21), Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 27
      by_cases hgt : mem0 20 > mem0 21
      · rw [Lst27gt mem0 hgt] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; have h := hgt; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
      · rw [Lst27le mem0 hgt] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
    · -- pc0 = 28
      rw [Lst28 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 29
      rw [Lst29 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have := hnnp 19 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hn19 (by omega); have h0 := hnnp 19 (by decide); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 19)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 19)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 19)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 19)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 19)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 19)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 19)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 19)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 19)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 19)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 19)]; exact hn18 (by omega)
      · intro h1; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19), Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19), Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact ht2120 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19), Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19), Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 30
      rw [Lst30 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 19) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 19) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 19)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 19)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 19)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 19)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 19)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 19)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 19)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 19)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 19)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 19)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 19)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 19)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 19)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 19)]; exact hn18 (by omega)
      · intro h1; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 19) h8; linarith [hr8]
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19), Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 19), Function.update_of_ne (by decide : (20:ℕ) ≠ 19)]; exact ht2120 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 19), Function.update_of_ne (by decide : (17:ℕ) ≠ 19)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 19), Function.update_of_ne (by decide : (13:ℕ) ≠ 19)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 31
      rw [Lst31 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have := hnnp 21 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 21)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have h := ht2120 (by omega) (by omega); have h20 := hr20; have hB := M_le_B r; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 21)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 21)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 21)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 21)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 21)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 21)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 21)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 21)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 21)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 21)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 21)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 21)]; exact hr20
      · rw [Function.update_self, hc3]; have h := ht2120 (by omega) (by omega); linarith [h, hr20]
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 21)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 21)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 21)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 21)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 21)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 21)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 21)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 21)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_self, Function.update_of_ne (by decide : (20:ℕ) ≠ 21), hc3]; have h := ht2120 (by omega) (by omega); linarith
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 21), Function.update_of_ne (by decide : (17:ℕ) ≠ 21)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 21), Function.update_of_ne (by decide : (13:ℕ) ≠ 21)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 32
      rw [Lst32 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 33
      by_cases he : mem0 19 = mem0 3
      · rw [Lst33eq mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro h1; omega
        · intro h1 h2; have h := ha1 (by omega); have h2 := hnnp 17 (by decide); linarith
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
      · rw [Lst33ne mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
    · -- pc0 = 34
      by_cases he : mem0 19 = mem0 9
      · rw [Lst34eq mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
      · rw [Lst34ne mem0 he] at h
        injection h with hpc hmem
        subst hpc
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hnnp
        · exact hm24
        · exact huniv
        · exact hr0
        · exact hc2
        · exact hc3
        · exact hc4
        · exact hc7
        · exact hr1
        · exact hr8
        · intro h1; omega
        · intro _; exact hr8pos (by omega)
        · exact hr9
        · intro h1; omega
        · exact hr13
        · exact hr15
        · exact hr17
        · exact hr20
        · exact hr21
        · exact hr22
        · exact hr24
        · exact hr22nn
        · intro _ _; exact hn10 (by omega) (by omega)
        · intro _; exact hn14 (by omega)
        · intro _; exact hn16 (by omega)
        · intro _; exact hn18 (by omega)
        · intro _; exact hn19 (by omega)
        · intro h1; omega
        · intro h1 h2; exact ht13 (by omega) (by omega)
        · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
        · intro h1 h2; omega
        · intro _; exact ha1 (by omega)
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; omega
        · intro h1 h2; exact hbit (by omega) (by omega)
        · intro h1; omega
    · -- pc0 = 35
      rw [Lst35 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1; omega
    · -- pc0 = 36
      rw [Lst36 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := hnnp 15 (by decide); have h2 := hnnp 17 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 15)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have ha := ha1 (by omega); have hb : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^(r-2) := (by simpa using hbit (by omega) (by omega)); have h17 := le_of_mul_pow_eq' (hnnp 17 (by decide)) hb; have h2 : (2:ℤ)^(r-2) * 2 = (2:ℤ)^(r-1) := two_mul_pow_pred_int (r-1) (by omega); have h3 := M_le_B r; have h4 : (2:ℤ)^(r-1) ≤ (2:ℤ)^r := pow_le_pow_right₀ (by norm_num) (by omega); linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 15)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 15)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 15)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 15)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 15)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 15)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 15)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 15)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 15)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]; exact hr13
      · rw [Function.update_self]; have ha := ha1 (by omega); have hb : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^(r-2) := (by simpa using hbit (by omega) (by omega)); have h17 := le_of_mul_pow_eq' (hnnp 17 (by decide)) hb; have h2 : (2:ℤ)^(r-2) * 2 = (2:ℤ)^(r-1) := two_mul_pow_pred_int (r-1) (by omega); have h3 := M_le_B r; have h4 : (2:ℤ)^(r-1) ≤ (2:ℤ)^r := pow_le_pow_right₀ (by norm_num) (by omega); linarith
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 15)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 15)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 15)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 15)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 15)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 15)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 15)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 15)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 15)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 15)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 15)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 15), Function.update_of_ne (by decide : (20:ℕ) ≠ 15)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_self, Function.update_of_ne (by decide : (17:ℕ) ≠ 15)]; linarith [ha1 (by omega)]
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 15), Function.update_of_ne (by decide : (13:ℕ) ≠ 15)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 37
      rw [Lst37 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h14 := hnnp 14 (by decide); have hb := hnnp 16 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 14)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h14 := hn14 (by omega); have h16 := hn16 (by omega); have h014 := hnnp 14 (by decide); have h016 := hnnp 16 (by decide); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 14)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 14)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 14)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 14)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 14)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 14)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 14)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 14)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 14)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 14)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 14)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 14)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 14)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 14)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 14)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 14)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact hn10 (by omega) (by omega)
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 14)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 14)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 14)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 14), Function.update_of_ne (by decide : (20:ℕ) ≠ 14)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 14), Function.update_of_ne (by decide : (17:ℕ) ≠ 14)]; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 14), Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 38
      rw [Lst38 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 14) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 14)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 14) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 14)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 14)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 14)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 14)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 14)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 14)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 14)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 14)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 14)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 14)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 14)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 14)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 14)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 14)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 14)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 14)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact hn10 (by omega) (by omega)
      · intro h1; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 14) h8; linarith [hr8]
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 14)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 14)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 14)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 14), Function.update_of_ne (by decide : (20:ℕ) ≠ 14)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 14), Function.update_of_ne (by decide : (17:ℕ) ≠ 14)]; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 14), Function.update_of_ne (by decide : (13:ℕ) ≠ 14)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 39
      rw [Lst39 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 40
      rw [Lst40 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 41
      rw [Lst41 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have := hnnp 16 (by decide); nlinarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h16 := hn16 (by omega); have h016 := hnnp 16 (by decide); have h2 := two_pow_sq r; nlinarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 16)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 16)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 16)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 16)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 16)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 16)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 16)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 16)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 16)]; exact hn14 (by omega)
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 16)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 16)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16), Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16), Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16), Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 42
      rw [Lst42 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (exact Int.emod_nonneg (mem0 16) (ne_of_gt (hr8pos (by omega)))) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 16) h8; have hb := huniv 8; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 16)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 16)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 16)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 16)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 16)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 16)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 16)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 16)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 16)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 16)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 16)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 16)]; exact hn14 (by omega)
      · intro h1; rw [Function.update_self]; have h8 := hr8pos (by omega); have hlt := Int.emod_lt_of_pos (mem0 16) h8; linarith [hr8]
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 16)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 16)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 16), Function.update_of_ne (by decide : (20:ℕ) ≠ 16)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 16), Function.update_of_ne (by decide : (17:ℕ) ≠ 16)]; exact ha2 (by omega) (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 16), Function.update_of_ne (by decide : (13:ℕ) ≠ 16)]; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 43
      rw [Lst43 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have := hnnp 17 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 17)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (have hb : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^(r-2) := (by simpa using hbit (by omega) (by omega)); have h17 := le_of_mul_pow_eq' (hnnp 17 (by decide)) hb; have h2 : (2:ℤ)^(r-2) * 2 = (2:ℤ)^(r-1) := two_mul_pow_pred_int (r-1) (by omega); have h3 := M_le_B r; have h4 : (2:ℤ)^(r-1) ≤ (2:ℤ)^r := pow_le_pow_right₀ (by norm_num) (by omega); linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 17)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 17)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 17)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 17)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 17)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 17)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 17)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 17)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 17)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 17)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 17)]; exact hr15
      · rw [Function.update_self]; have hb : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^(r-2) := (by simpa using hbit (by omega) (by omega)); have h17 := le_of_mul_pow_eq' (hnnp 17 (by decide)) hb; have h2 : (2:ℤ)^(r-2) * 2 = (2:ℤ)^(r-1) := two_mul_pow_pred_int (r-1) (by omega); have h3 := M_le_B r; have h4 : (2:ℤ)^(r-1) ≤ (2:ℤ)^r := pow_le_pow_right₀ (by norm_num) (by omega); linarith
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 17)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 17)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 17)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 17)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 17)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 17)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 17)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 17)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 17)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 17)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 17)]; exact ht13 (by omega) (by omega)
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 17), Function.update_of_ne (by decide : (20:ℕ) ≠ 17)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 17), Function.update_self]; linarith [ha2 (by omega) (by omega)]
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; rw [Function.update_self, Function.update_of_ne (by decide : (13:ℕ) ≠ 17)]; have h : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^(r-2) := (by simpa using hbit (by omega) (by omega)); show (mem0 17 + mem0 17) * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^((r-2)+1); rw [pow_succ]; nlinarith [h]
      · intro h1; omega
    · -- pc0 = 44
      rw [Lst44 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (have h := ht13 (by omega) (by omega); rw [hc3]; linarith) | (exact hnnp i hi)
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 13)]; exact hm24
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc3]; have := huniv 13; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 13)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 13)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 13)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 13)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 13)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 13)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 13)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 13)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 13)]; exact hr9
      · intro h1; omega
      · rw [Function.update_self, hc3]; linarith [hr13]
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 13)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 13)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 13)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 13)]; exact hr22
      · rw [Function.update_of_ne (by decide : (24:ℕ) ≠ 13)]; exact hr24
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 13)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 13)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 13)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 13)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 13)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 13), Function.update_of_ne (by decide : (20:ℕ) ≠ 13)]; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 13), Function.update_of_ne (by decide : (17:ℕ) ≠ 13)]; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; have hb : mem0 17 * (2:ℤ)^((mem0 13).toNat) = (2:ℤ)^((r-2)+1) := hbit (by omega) (by omega); have ht : (mem0 13 - 1).toNat = (mem0 13).toNat - 1 := (by have := ht13 (by omega) (by omega); omega); rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 13)]; rw [Function.update_self]; rw [hc3]; rw [ht]; rw [show r - 2 + (if 45 = 44 then 1 else 0) = r - 2 from by simp]; exact dbl_step (by omega) hb
      · intro h1; omega
    · -- pc0 = 45
      rw [Lst45 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnnp
      · exact hm24
      · exact huniv
      · exact hr0
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc7
      · exact hr1
      · exact hr8
      · intro h1; omega
      · intro _; exact hr8pos (by omega)
      · exact hr9
      · intro h1; omega
      · exact hr13
      · exact hr15
      · exact hr17
      · exact hr20
      · exact hr21
      · exact hr22
      · exact hr24
      · exact hr22nn
      · intro _ _; exact hn10 (by omega) (by omega)
      · intro _; exact hn14 (by omega)
      · intro _; exact hn16 (by omega)
      · intro _; exact hn18 (by omega)
      · intro _; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; exact hsqn (by omega) (by omega) (by omega) (by omega)
      · intro h1 h2; omega
      · intro _; exact ha1 (by omega)
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; exact hbit (by omega) (by omega)
      · intro h1; omega
    · -- pc0 = 46
      rw [Lst46 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2]; have := hnnp 15 (by decide); linarith) | (exact hnnp i hi)
      · rw [Function.update_self, hc2, add_zero]; have := hnnp 15 (by decide); linarith
      · intro i; rw [Function.update_apply]; split_ifs with hid <;> first | (rw [hc2, add_zero]; have := huniv 15; linarith) | (exact huniv i)
      · rw [Function.update_of_ne (by decide : (0:ℕ) ≠ 24)]; exact hr0
      · rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 24)]; exact hc2
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 24)]; exact hc3
      · rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 24)]; exact hc4
      · rw [Function.update_of_ne (by decide : (7:ℕ) ≠ 24)]; exact hc7
      · rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 24)]; exact hr1
      · rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 24)]; exact hr8
      · intro h1; omega
      · intro _; rw [Function.update_of_ne (by decide : (8:ℕ) ≠ 24)]; exact hr8pos (by omega)
      · rw [Function.update_of_ne (by decide : (9:ℕ) ≠ 24)]; exact hr9
      · intro h1; omega
      · rw [Function.update_of_ne (by decide : (13:ℕ) ≠ 24)]; exact hr13
      · rw [Function.update_of_ne (by decide : (15:ℕ) ≠ 24)]; exact hr15
      · rw [Function.update_of_ne (by decide : (17:ℕ) ≠ 24)]; exact hr17
      · rw [Function.update_of_ne (by decide : (20:ℕ) ≠ 24)]; exact hr20
      · rw [Function.update_of_ne (by decide : (21:ℕ) ≠ 24)]; exact hr21
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 24)]; exact hr22
      · rw [Function.update_self, hc2, add_zero]; exact hr15
      · rw [Function.update_of_ne (by decide : (22:ℕ) ≠ 24)]; exact hr22nn
      · intro _ _; rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 24)]; exact hn10 (by omega) (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (14:ℕ) ≠ 24)]; exact hn14 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (16:ℕ) ≠ 24)]; exact hn16 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (18:ℕ) ≠ 24)]; exact hn18 (by omega)
      · intro _; rw [Function.update_of_ne (by decide : (19:ℕ) ≠ 24)]; exact hn19 (by omega)
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2 h3 h4; omega
      · intro h1 h2; omega
      · intro h1; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1 h2; omega
      · intro h1; omega
    · -- pc0 = 47
      rw [Lst47 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      exact h0all
    · -- pc0 = 48
      rw [Lst48 mem0] at h
      injection h with hpc hmem
      subst hpc
      subst hmem
      exact h0all
  · have hnone : Lprog[pc0]? = none := by rw [List.getElem?_eq_none_iff]; simp [Lprog]; omega
    simp only [Lstep, hnone] at h
    injection h with hpc hmem
    subst hpc
    subst hmem
    exact h0all


theorem ainv_run (r p : ℕ) (hr : 3 ≤ r) (hp1 : 1 ≤ p) (hpu : p < 2^r) :
    ∀ t, ∀ pc ms, Lrun t (Ls0 r p) = ⟨pc, ms⟩ → AInv r pc ms := by
  intro t
  induction t with
  | zero =>
    intro pc ms h
    simp only [Lrun_zero] at h
    injection h with hpc hmem
    subst hpc; subst hmem
    exact ainv_init r p hr hp1 hpu
  | succ t ih =>
    intro pc ms h
    have hst : Lrun t (Ls0 r p) = ⟨(Lrun t (Ls0 r p)).pc, (Lrun t (Ls0 r p)).mem⟩ := rfl
    rw [Lrun_succ, hst] at h
    exact ainv_step r hr _ _ pc ms (ih _ _ rfl) h

/-- **Lemma 1** (amplitude-equipped form): the concrete program `Lprog` halts within
`40*(r+1)^2 + 100` steps on every odd `p` with `1 ≤ p < 2^r`, computing `ind_5 p` (in
`mem 24`) when `p ∈ ⟨5⟩` and `-1` otherwise; moreover *throughout the run every register
stays in `[-1, 2^(2r)]`*, the amplitude bound for logarithm computation. -/
theorem lemma1_amp (r p : ℕ) (hr : 3 ≤ r) (hodd : Odd p) (hp1 : 1 ≤ p) (hpu : p < 2^r) :
    ∃ T ≤ 40*(r+1)*(r+1) + 100, ∃ st : State, Lrun T (Ls0 r p) = st ∧
      ((st.pc = 47 ∧ ∃ a : ℕ, a < 2^(r-2) ∧ ((p : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r))^a
          ∧ st.mem 24 = (a : ℤ))
       ∨ (st.pc = 48 ∧ st.mem 24 = -1 ∧
          ∀ a : ℕ, a < 2^(r-2) → ((p : ℤ) : ZMod (2^r)) ≠ (5 : ZMod (2^r))^a)) ∧
      (∀ t ≤ T, ∀ pc ms, Lrun t (Ls0 r p) = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ (2:ℤ)^(2*r)) := by
  obtain ⟨T, hT, st, hrun, hout⟩ := lemma1 r p hr hodd hp1 hpu
  refine ⟨T, hT, st, hrun, hout, ?_⟩
  intro t ht pc ms h i
  have hA := ainv_run r p hr hp1 hpu t pc ms h
  refine ⟨?_, hA.univ i⟩
  by_cases hi : i = 24
  · subst hi; exact hA.m24
  · exact le_trans (by norm_num : (-1:ℤ) ≤ 0) (hA.nnp i hi)

end BkSet.RAM

end


-- ===============================================================================================
-- ============  Section `Theorem1` proving facts about merging RAM-programs  ====================
-- ===============================================================================================

section

/-
# Discrete logarithms and the merged algorithm of Theorem 1

## What is in this file

The paper proves

* **Lemma 1**: a RAM program computing `ind_5 p` modulo `2^r` in `O(r^2)` steps (formalised in
  `RamLog` as `BkSet.RAM.lemma1` and `BkSet.RAM.lemma1_amp`), and
* **Theorem 1**: the algorithm computing the set `H[n,k]` obtained by *merging* the
  prime-generation program of `PrimeGen` section with the discrete-logarithm program.

This file formalises the merge step ("two programs can be merged, and the time and amplitude
bounds are at most the sums of the bounds of the parts") and the *`N`-fold generalisation of
Lemma 1* ("compute not one but `N` discrete logarithms in the same group"), which is the part
of Theorem 1 that involves the logarithm routine.

### 1. Merging two RAM programs

`Run P t s` is the generic `t`-step execution of an arbitrary instruction list `P`
(so `BkSet.RAM.run = Run BkSet.RAM.prog`), and `shiftProg off P` shifts all *jump targets* of
`P` by `off`.  The two key results are

* `Run_append_shift` : running `pre ++ shiftProg pre.length P2` from pc `pre.length + q`
  simulates `P2` from pc `q`, and
* `Run_concat` : if `P1`, started from `s`, reaches pc `P1.length` at time `T1` (and stays
  strictly below it before that), then `P1 ++ shiftProg P1.length P2` runs `P2` on the
  resulting memory for an additional `T2` steps.  This is the formal "merge" of two programs:
  the step bound is `T1 + T2` and the register bound is the maximum of the two parts.

### 2. The `N`-fold lemma

`blk inp out` is the concrete "one logarithm" block: it resets the log-routine registers
(`rprog`), runs the log program with the halt instructions replaced by stores into `out`
(`Ltail`), and therefore computes `ind_5 (mem inp)` (or `-1`) into `mem out` in
`18 + O(r^2)` steps, preserving the input registers and the constants.  `Nprog L` is the
merging of one such block per pair `(inp, out) ∈ L`, and

* `Nprog_spec` : running `Nprog L` computes *all* the logarithms in `L`, in at most
  `L.length * (18 + 40*(r+1)^2 + 100)` steps, preserving the registers that are not outputs;
* `lemma1_N` : the same statement in the paper's language -- the `N`-fold generalisation of
  Lemma 1.

### 3. Intermediate infrastructure

* `Lrun_agree` / `Op.exec_agree` : two memories that agree on the registers `0..24` produce
  identical log-program runs (used to replay `lemma1` on any block).
* `lt_log` : the *first* time the log program reaches its halt pc `47`/`48`, together with the
  output guarantee of `lemma1` at that time.
* `Lrun_consts` / `Run_frame` : the log program never writes the constant registers
  `2,3,4,5,6,7,11,12,23`, and instructions only write inside prescribed sets.
* `rprog_spec` : the 16-instruction register-reset of one block, and `blk_spec` : the full
  one-block specification (halt time, first-halt property, output, frame).

### 4. Status of Theorem 1

Everything needed for the *logarithm* half of Theorem 1 is proved here.  The remaining glue
for the fully merged Theorem-1 algorithm is:

* a small `setup` program run between the two parts which (a) fixes the constant registers
  `2,3,4,5,6,7,11,12,23` expected by the log routine (the prime generator uses `2 = 1`,
  `3 = 2`), (b) copies the modulus exponent `r` into register `25`, (c) computes `2^r` by a
  doubling loop (so that `-p_i mod 2^r = 2^r - p_i` can be fed to the routine) and (d) prepares
  the `n` inputs `p_i` and `n` inputs `2^r - p_i` in registers `≥ 25`;
* the register transfer of the prime generator's halting memory into the initial memory of
  `Nprog`, i.e. replaying `BkSet.RAM.main_bounded_all` through a memory that additionally
  carries `r` in a high register; the only delicate point is that the generator's (data
  dependent) `store` must not overwrite that register, which follows from the amplitude bound
  `mem 15 ≤ p_n + 1001 < R`;
* assembling the three pieces with `Run_concat`, and combining the amplitude bounds
  `≤ p_n + 1001` (prime generator) and `∈ [-1, 2^(2r)]` (log routine) into the final
  `-1 .. 2^(2r) + O(1)` bound of Theorem 1.

Once `setup` is composed with `Nprog` in the same way as above, Theorem 1 follows by two
applications of `Run_concat`, giving the step bound
`O(n^4) + 2n * (18 + 40*(r+1)^2 + 100) = O(n^4 + n r^2)`.
-/


namespace BkSet.RAM
open Nat

set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-! ## Generic program execution, shifting, concatenation -/

def stepP (P : List Op) (s : State) : State :=
  match P[s.pc]? with
  | some op => op.exec s
  | none => s

def Run (P : List Op) : ℕ → State → State
  | 0, s => s
  | (k+1), s => stepP P (Run P k s)

@[simp] theorem Run_zero (P : List Op) (s : State) : Run P 0 s = s := rfl
@[simp] theorem Run_succ (P : List Op) (k : ℕ) (s : State) :
    Run P (k+1) s = stepP P (Run P k s) := rfl

theorem Run_add (P : List Op) (a b : ℕ) (s : State) :
    Run P (a+b) s = Run P b (Run P a s) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, Run_succ, Run_succ, ih]

theorem stepP_prog (s : State) : stepP prog s = step s := rfl

theorem Run_prog (t : ℕ) (s : State) : Run prog t s = run t s := by
  induction t generalizing s with
  | zero => simp
  | succ t ih => rw [Run_succ, ih, stepP_prog, run_succ]

theorem state_pc_eq {s : State} {pc : ℕ} (h : s.pc = pc) : s = ⟨pc, s.mem⟩ := by
  cases s with | mk p m => simp_all

def shiftOp (off : ℕ) : Op → Op
  | .jgt a b L => .jgt a b (L+off)
  | .jeq a b L => .jeq a b (L+off)
  | .jmp L => .jmp (L+off)
  | op => op

def shiftProg (off : ℕ) (P : List Op) : List Op := P.map (shiftOp off)

theorem shiftProg_length (off : ℕ) (P : List Op) : (shiftProg off P).length = P.length := by
  simp [shiftProg]

theorem shiftOp_exec (off : ℕ) (op : Op) (s : State) :
    (shiftOp off op).exec ⟨off + s.pc, s.mem⟩ = ⟨off + (op.exec s).pc, (op.exec s).mem⟩ := by
  match op with
  | .add d a b => simp [shiftOp, Op.exec] <;> omega
  | .sub d a b => simp [shiftOp, Op.exec] <;> omega
  | .mul d a b => simp [shiftOp, Op.exec] <;> omega
  | .quo d a b => simp [shiftOp, Op.exec] <;> omega
  | .rem d a b => simp [shiftOp, Op.exec] <;> omega
  | .load d a => simp [shiftOp, Op.exec] <;> omega
  | .store a b => simp [shiftOp, Op.exec] <;> omega
  | .jgt a b L => by_cases h : s.mem a > s.mem b <;> simp [shiftOp, Op.exec, h] <;> omega
  | .jeq a b L => by_cases h : s.mem a = s.mem b <;> simp [shiftOp, Op.exec, h] <;> omega
  | .jmp L => simp [shiftOp, Op.exec] <;> omega
  | .halt => simp [shiftOp, Op.exec] <;> omega

theorem getElem?_shift (off : ℕ) (P : List Op) (q : ℕ) :
    (shiftProg off P)[q]? = (P[q]?).map (shiftOp off) := by
  simp [shiftProg, List.getElem?_map]

theorem getElem?_append_at (pre S : List Op) (q : ℕ) :
    (pre ++ S)[pre.length + q]? = S[q]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem stepP_append_shift (pre P2 : List Op) (q : ℕ) (mem : ℕ → ℤ) :
    stepP (pre ++ shiftProg pre.length P2) ⟨pre.length + q, mem⟩
      = ⟨pre.length + (stepP P2 ⟨q, mem⟩).pc, (stepP P2 ⟨q, mem⟩).mem⟩ := by
  cases h : P2[q]? with
  | none =>
    have h1 : stepP P2 ⟨q, mem⟩ = ⟨q, mem⟩ := by simp only [stepP, h]
    rw [h1]
    simp only [stepP]
    rw [getElem?_append_at, getElem?_shift, h]
    simp
  | some op =>
    have h1 : stepP P2 ⟨q, mem⟩ = op.exec ⟨q, mem⟩ := by simp only [stepP, h]
    rw [h1]
    simp only [stepP]
    rw [getElem?_append_at, getElem?_shift, h]
    simp only [Option.map_some]
    exact shiftOp_exec pre.length op ⟨q, mem⟩

theorem Run_append_shift (pre P2 : List Op) (T : ℕ) (q : ℕ) (mem : ℕ → ℤ) :
    Run (pre ++ shiftProg pre.length P2) T ⟨pre.length + q, mem⟩
      = ⟨pre.length + (Run P2 T ⟨q, mem⟩).pc, (Run P2 T ⟨q, mem⟩).mem⟩ := by
  induction T generalizing q mem with
  | zero => simp
  | succ T ih =>
    rw [Run_succ, ih q mem, Run_succ]
    exact stepP_append_shift pre P2 (Run P2 T ⟨q, mem⟩).pc (Run P2 T ⟨q, mem⟩).mem

theorem stepP_eq_of_lt (P1 S : List Op) (s : State) (h : s.pc < P1.length) :
    stepP (P1 ++ S) s = stepP P1 s := by
  have h1 : (P1 ++ S)[s.pc]? = P1[s.pc]? := List.getElem?_append_left h
  simp only [stepP]
  rw [h1]

theorem Run_prefix (P1 S : List Op) (T1 : ℕ) (s : State)
    (hpc : ∀ t < T1, (Run P1 t s).pc < P1.length) :
    ∀ t ≤ T1, Run (P1 ++ S) t s = Run P1 t s := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ T1 := by omega
    rw [Run_succ, Run_succ, ih ht']
    exact stepP_eq_of_lt P1 S (Run P1 t s) (hpc t (by omega))

theorem Run_concat (P1 P2 : List Op) (T1 T2 : ℕ) (s : State)
    (hpc : ∀ t < T1, (Run P1 t s).pc < P1.length)
    (hhit : (Run P1 T1 s).pc = P1.length) :
    Run (P1 ++ shiftProg P1.length P2) (T1 + T2) s
      = ⟨P1.length + (Run P2 T2 ⟨0, (Run P1 T1 s).mem⟩).pc,
          (Run P2 T2 ⟨0, (Run P1 T1 s).mem⟩).mem⟩ := by
  rw [Run_add]
  have h1 : Run (P1 ++ shiftProg P1.length P2) T1 s = Run P1 T1 s :=
    Run_prefix P1 _ T1 s hpc T1 le_rfl
  rw [h1, state_pc_eq hhit]
  exact Run_append_shift P1 P2 T2 0 (Run P1 T1 s).mem

/-! ## Register-bounded instructions and memory agreement -/

def OpSmall (N : ℕ) : Op → Prop
  | .add d a b => d ≤ N ∧ a ≤ N ∧ b ≤ N
  | .sub d a b => d ≤ N ∧ a ≤ N ∧ b ≤ N
  | .mul d a b => d ≤ N ∧ a ≤ N ∧ b ≤ N
  | .quo d a b => d ≤ N ∧ a ≤ N ∧ b ≤ N
  | .rem d a b => d ≤ N ∧ a ≤ N ∧ b ≤ N
  | .load d a => False
  | .store a b => a ≤ N ∧ b ≤ N
  | .jgt a b L => a ≤ N ∧ b ≤ N
  | .jeq a b L => a ≤ N ∧ b ≤ N
  | .jmp L => True
  | .halt => True

instance decidableOpSmall (N : ℕ) (op : Op) : Decidable (OpSmall N op) := by
  cases op <;> (simp only [OpSmall] <;> infer_instance)

theorem Op.exec_agree {N : ℕ} {op : Op} (h : OpSmall N op) {pc : ℕ} {m m' : ℕ → ℤ}
    (hm : ∀ i, i ≤ N → m i = m' i) :
    (op.exec ⟨pc, m⟩).pc = (op.exec ⟨pc, m'⟩).pc ∧
      ∀ i, i ≤ N → (op.exec ⟨pc, m⟩).mem i = (op.exec ⟨pc, m'⟩).mem i := by
  match op with
  | .add d a b | .sub d a b | .mul d a b | .quo d a b | .rem d a b =>
    obtain ⟨hd, ha, hb⟩ := h
    refine ⟨rfl, fun i hi => ?_⟩
    simp only [Op.exec, Function.update_apply]
    by_cases hid : i = d
    · rw [if_pos hid, if_pos hid, hm a ha, hm b hb]
    · rw [if_neg hid, if_neg hid]; exact hm i hi
  | .load d a => exact h.elim
  | .store a b =>
    obtain ⟨ha, hb⟩ := h
    have hadr : (m a).toNat = (m' a).toNat := by rw [hm a ha]
    refine ⟨rfl, fun i hi => ?_⟩
    simp only [Op.exec, Function.update_apply, hadr]
    by_cases hid : i = (m' a).toNat
    · rw [if_pos hid, if_pos hid, hm b hb]
    · rw [if_neg hid, if_neg hid]; exact hm i hi
  | .jgt a b L =>
    obtain ⟨ha, hb⟩ := h
    have hc : (m a > m b) ↔ (m' a > m' b) := by rw [hm a ha, hm b hb]
    refine ⟨?_, fun i hi => hm i hi⟩
    simp only [Op.exec]
    by_cases hcond : m a > m b
    · rw [if_pos hcond, if_pos (hc.mp hcond)]
    · rw [if_neg hcond, if_neg (fun hh => hcond (hc.mpr hh))]
  | .jeq a b L =>
    obtain ⟨ha, hb⟩ := h
    have hc : (m a = m b) ↔ (m' a = m' b) := by rw [hm a ha, hm b hb]
    refine ⟨?_, fun i hi => hm i hi⟩
    simp only [Op.exec]
    by_cases hcond : m a = m b
    · rw [if_pos hcond, if_pos (hc.mp hcond)]
    · rw [if_neg hcond, if_neg (fun hh => hcond (hc.mpr hh))]
  | .jmp L => exact ⟨rfl, fun i hi => hm i hi⟩
  | .halt => exact ⟨rfl, fun i hi => hm i hi⟩

theorem Lprog_small : ∀ op ∈ Lprog, OpSmall 24 op := by decide

theorem Lstep_agree {pc : ℕ} {m m' : ℕ → ℤ} (h : ∀ i, i ≤ 24 → m i = m' i) :
    (Lstep ⟨pc, m⟩).pc = (Lstep ⟨pc, m'⟩).pc ∧
      ∀ i, i ≤ 24 → (Lstep ⟨pc, m⟩).mem i = (Lstep ⟨pc, m'⟩).mem i := by
  simp only [Lstep]
  cases hop : Lprog[pc]? with
  | none => exact ⟨rfl, h⟩
  | some op =>
    have hmem : op ∈ Lprog := by rw [List.mem_iff_getElem?]; exact ⟨pc, hop⟩
    simp only [hop]
    exact Op.exec_agree (Lprog_small op hmem) h

theorem Lrun_agree (T pc : ℕ) (m m' : ℕ → ℤ) (h : ∀ i, i ≤ 24 → m i = m' i) :
    (Lrun T ⟨pc, m⟩).pc = (Lrun T ⟨pc, m'⟩).pc ∧
      ∀ i, i ≤ 24 → (Lrun T ⟨pc, m⟩).mem i = (Lrun T ⟨pc, m'⟩).mem i := by
  induction T generalizing pc m m' with
  | zero => exact ⟨rfl, h⟩
  | succ T ih =>
    obtain ⟨hp, hm⟩ := ih pc m m' h
    have hs : Lrun T ⟨pc, m⟩ = (⟨(Lrun T ⟨pc, m⟩).pc, (Lrun T ⟨pc, m⟩).mem⟩ : State) :=
      state_pc_eq rfl
    have hs' : Lrun T ⟨pc, m'⟩ = (⟨(Lrun T ⟨pc, m⟩).pc, (Lrun T ⟨pc, m'⟩).mem⟩ : State) :=
      state_pc_eq hp.symm
    have h2 := Lstep_agree (pc := (Lrun T ⟨pc, m⟩).pc) hm
    rw [Lrun_succ, Lrun_succ, hs, hs']
    exact h2

/-! ## Jump-target bounds and `pc` bounds -/

def OpBounded (N : ℕ) : Op → Prop
  | .jgt _ _ L => L ≤ N
  | .jeq _ _ L => L ≤ N
  | .jmp L => L ≤ N
  | _ => True

theorem OpBounded.exec_pc_le {N : ℕ} {op : Op} (h : OpBounded N op) {s : State}
    (hs : s.pc < N) : (op.exec s).pc ≤ N := by
  match op with
  | .add d a b => simp only [Op.exec]; omega
  | .sub d a b => simp only [Op.exec]; omega
  | .mul d a b => simp only [Op.exec]; omega
  | .quo d a b => simp only [Op.exec]; omega
  | .rem d a b => simp only [Op.exec]; omega
  | .load d a => simp only [Op.exec]; omega
  | .store a b => simp only [Op.exec]; omega
  | .jgt a b L =>
    have hL : L ≤ N := h
    by_cases hc : s.mem a > s.mem b
    · simp only [Op.exec, if_pos hc]; omega
    · simp only [Op.exec, if_neg hc]; omega
  | .jeq a b L =>
    have hL : L ≤ N := h
    by_cases hc : s.mem a = s.mem b
    · simp only [Op.exec, if_pos hc]; omega
    · simp only [Op.exec, if_neg hc]; omega
  | .jmp L => have hL : L ≤ N := h; simp only [Op.exec]; omega
  | .halt => simp only [Op.exec]; omega

theorem Run_pc_le (P : List Op) (h : ∀ op ∈ P, OpBounded P.length op)
    (s : State) (hs : s.pc ≤ P.length) : ∀ t, (Run P t s).pc ≤ P.length := by
  intro t
  induction t generalizing s with
  | zero => simpa using hs
  | succ t ih =>
    set x := Run P t s with hx
    have hxle : x.pc ≤ P.length := ih s hs
    rw [Run_succ, ← hx]
    cases hop : P[x.pc]? with
    | none => simp only [stepP, hop]; exact hxle
    | some op =>
      have hmem : op ∈ P := by rw [List.mem_iff_getElem?]; exact ⟨x.pc, hop⟩
      have hlt : x.pc < P.length := by
        by_contra hc
        have hnone : P[x.pc]? = none := by
          rw [List.getElem?_eq_none_iff]; omega
        rw [hop] at hnone; exact absurd hnone (by simp)
      simp only [stepP, hop]
      exact OpBounded.exec_pc_le (h op hmem) hlt

end BkSet.RAM

namespace BkSet.RAM
open Nat

/-! ## `pc` bounds for `Lprog` -/

theorem Lstep_pc_le48 (m : ℕ → ℤ) {pc : ℕ} (h : pc ≤ 48) : (Lstep ⟨pc, m⟩).pc ≤ 48 := by
  interval_cases pc <;>
    simp only [Lstep, Lprog, Op.exec, List.getElem?_cons_zero, List.getElem?_cons_succ] <;>
    (try (split <;> omega)) <;> omega

theorem Lrun_pc_le48 (r q : ℕ) : ∀ t, (Lrun t (Ls0 r q)).pc ≤ 48 := by
  intro t
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih => rw [Lrun_succ]; exact Lstep_pc_le48 _ ih

/-! ## The general prefix-agreement lemma -/

theorem Run_prefix_eq (P Q : List Op) (h1 T1 : ℕ) (s : State)
    (hagree : ∀ i, i < h1 → Q[i]? = P[i]?)
    (hpc : ∀ t < T1, (Run P t s).pc < h1) :
    ∀ t ≤ T1, Run Q t s = Run P t s := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ T1 := by omega
    rw [Run_succ, Run_succ, ih ht']
    have hp := hpc t (by omega)
    have hq : Q[(Run P t s).pc]? = P[(Run P t s).pc]? := hagree _ hp
    simp only [stepP]
    rw [hq]

/-! ## Halt-time characterisation of `Lprog` -/

theorem Lstep_self_halt (m : ℕ → ℤ) {pc : ℕ} (h : pc = 47 ∨ pc = 48) :
    Lstep ⟨pc, m⟩ = ⟨pc, m⟩ := by
  rcases h with rfl | rfl
  · exact Lst47 m
  · exact Lst48 m

theorem Lrun_stuck (r q : ℕ) {T1 : ℕ} (h : 47 ≤ (Lrun T1 (Ls0 r q)).pc) :
    ∀ t, T1 ≤ t → Lrun t (Ls0 r q) = Lrun T1 (Ls0 r q) := by
  have hle : (Lrun T1 (Ls0 r q)).pc ≤ 48 := Lrun_pc_le48 r q T1
  have hpc : (Lrun T1 (Ls0 r q)).pc = 47 ∨ (Lrun T1 (Ls0 r q)).pc = 48 := by omega
  intro t ht
  induction t with
  | zero =>
    have h0 : T1 = 0 := by omega
    rw [h0]
  | succ t ih =>
    rcases Nat.lt_or_ge T1 (t+1) with hlt | hge
    · have h2 : T1 ≤ t := by omega
      rw [Lrun_succ, ih h2, state_pc_eq (s := Lrun T1 (Ls0 r q)) rfl]
      exact Lstep_self_halt _ hpc
    · have h2 : T1 = t+1 := by omega
      rw [h2]

theorem lt_log (r q : ℕ) (hr : 3 ≤ r) (hodd : Odd q) (hq1 : 1 ≤ q) (hqu : q < 2^r) :
    ∃ TL ≤ 40*(r+1)*(r+1)+100,
      (∀ t < TL, (Lrun t (Ls0 r q)).pc < 47) ∧
      (((Lrun TL (Ls0 r q)).pc = 47 ∧ ∃ a : ℕ, a < 2^(r-2) ∧
          ((q : ℤ): ZMod (2^r)) = (5 : ZMod (2^r))^a ∧ (Lrun TL (Ls0 r q)).mem 24 = (a : ℤ))
       ∨ ((Lrun TL (Ls0 r q)).pc = 48 ∧ (Lrun TL (Ls0 r q)).mem 24 = -1 ∧
          ∀ a, a < 2^(r-2) → ((q : ℤ): ZMod (2^r)) ≠ (5 : ZMod (2^r))^a)) := by
  obtain ⟨T, hT, st, hrun, hout⟩ := lemma1 r q hr hodd hq1 hqu
  have hex : ∃ t, 47 ≤ (Lrun t (Ls0 r q)).pc :=
    ⟨T, by rw [hrun]; rcases hout with ⟨h,_⟩ | ⟨h,_⟩ <;> omega⟩
  have hTLspec : 47 ≤ (Lrun (Nat.find hex) (Ls0 r q)).pc := Nat.find_spec hex
  have hTLle : Nat.find hex ≤ T :=
    Nat.find_min' hex (by rw [hrun]; rcases hout with ⟨h,_⟩ | ⟨h,_⟩ <;> omega)
  have hstuck : Lrun T (Ls0 r q) = Lrun (Nat.find hex) (Ls0 r q) :=
    Lrun_stuck r q hTLspec T hTLle
  refine ⟨Nat.find hex, by omega, ?_, ?_⟩
  · intro t ht
    by_contra hc
    exact Nat.find_min hex ht (by omega)
  · rcases hout with ⟨hpc, a, ha, hq, h24⟩ | ⟨hpc, h24, hne⟩
    · refine Or.inl ⟨?_, a, ha, hq, ?_⟩
      · rw [← hstuck, hrun, hpc]
      · rw [← hstuck, hrun, h24]
    · refine Or.inr ⟨?_, ?_, hne⟩
      · rw [← hstuck, hrun, hpc]
      · rw [← hstuck, hrun, h24]

/-! ## The `Ltail` program (halts replaced by stores) -/

def Ltail (out : ℕ) : List Op :=
  Lprog.take 47 ++ [Op.add out 24 2, Op.add out 24 2]

theorem Ltail_length (out : ℕ) : (Ltail out).length = 49 := by
  simp [Ltail, Lprog]

theorem take47_len : (Lprog.take 47).length = 47 := by simp [Lprog]

theorem Ltail_getElem?_lt (out i : ℕ) (h : i < 47) : (Ltail out)[i]? = Lprog[i]? := by
  rw [Ltail, List.getElem?_append_left (by rw [take47_len]; exact h), List.getElem?_take_of_lt h]

theorem Ltail_getElem?_47 (out : ℕ) : (Ltail out)[47]? = some (Op.add out 24 2) := by
  rw [Ltail, List.getElem?_append_right (by rw [take47_len]), take47_len]
  simp [List.getElem?_cons_zero]

theorem Ltail_getElem?_48 (out : ℕ) : (Ltail out)[48]? = some (Op.add out 24 2) := by
  rw [Ltail, List.getElem?_append_right (by rw [take47_len]; omega), take47_len]
  simp [List.getElem?_cons_zero]

/-! ## `Lprog` preserves the constant registers -/

theorem Lstep_mem_ne (m : ℕ → ℤ) {pc i : ℕ} (hpc : pc ≤ 48)
    (hi : i ≠ 8 ∧ i ≠ 22 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 16 ∧ i ≠ 13 ∧ i ≠ 18 ∧ i ≠ 20 ∧
          i ≠ 19 ∧ i ≠ 21 ∧ i ≠ 15 ∧ i ≠ 14 ∧ i ≠ 17 ∧ i ≠ 24) :
    (Lstep ⟨pc, m⟩).mem i = m i := by
  interval_cases pc <;>
    simp only [Lstep, Lprog, Op.exec, Function.update_apply, List.getElem?_cons_zero,
      List.getElem?_cons_succ] <;>
    (try (split_ifs)) <;> simp_all

theorem Lstep_consts (m : ℕ → ℤ) {pc : ℕ} (hpc : pc ≤ 48) :
    (Lstep ⟨pc, m⟩).mem 2 = m 2 ∧ (Lstep ⟨pc, m⟩).mem 3 = m 3 ∧
    (Lstep ⟨pc, m⟩).mem 4 = m 4 ∧ (Lstep ⟨pc, m⟩).mem 5 = m 5 ∧
    (Lstep ⟨pc, m⟩).mem 6 = m 6 ∧ (Lstep ⟨pc, m⟩).mem 7 = m 7 ∧
    (Lstep ⟨pc, m⟩).mem 11 = m 11 ∧ (Lstep ⟨pc, m⟩).mem 12 = m 12 ∧
    (Lstep ⟨pc, m⟩).mem 23 = m 23 :=
  ⟨Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide),
   Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide),
   Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide), Lstep_mem_ne m hpc (by decide)⟩

theorem Lrun_consts (r q : ℕ) (t : ℕ) :
    (Lrun t (Ls0 r q)).mem 2 = (LinitMem r q) 2 ∧
    (Lrun t (Ls0 r q)).mem 3 = (LinitMem r q) 3 ∧
    (Lrun t (Ls0 r q)).mem 4 = (LinitMem r q) 4 ∧
    (Lrun t (Ls0 r q)).mem 5 = (LinitMem r q) 5 ∧
    (Lrun t (Ls0 r q)).mem 6 = (LinitMem r q) 6 ∧
    (Lrun t (Ls0 r q)).mem 7 = (LinitMem r q) 7 ∧
    (Lrun t (Ls0 r q)).mem 11 = (LinitMem r q) 11 ∧
    (Lrun t (Ls0 r q)).mem 12 = (LinitMem r q) 12 ∧
    (Lrun t (Ls0 r q)).mem 23 = (LinitMem r q) 23 := by
  have key : ∀ i, i ∈ ({2,3,4,5,6,7,11,12,23} : Finset ℕ) →
      (Lrun t (Ls0 r q)).mem i = (LinitMem r q) i := by
    intro i hi
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Lrun_succ]
      have hpc : (Lrun t (Ls0 r q)).pc ≤ 48 := Lrun_pc_le48 r q t
      have hne : i ≠ 8 ∧ i ≠ 22 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 16 ∧ i ≠ 13 ∧ i ≠ 18 ∧ i ≠ 20 ∧
          i ≠ 19 ∧ i ≠ 21 ∧ i ≠ 15 ∧ i ≠ 14 ∧ i ≠ 17 ∧ i ≠ 24 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        omega
      rw [Lstep_mem_ne _ hpc hne]
      exact ih
  exact ⟨key 2 (by decide), key 3 (by decide), key 4 (by decide), key 5 (by decide),
    key 6 (by decide), key 7 (by decide), key 11 (by decide), key 12 (by decide),
    key 23 (by decide)⟩

/-! ## The per-block reset program -/

def rprog (inp : ℕ) : List Op :=
  [ Op.add 1 inp 2, Op.add 0 25 2, Op.sub 8 2 2, Op.sub 9 2 2, Op.sub 10 2 2,
    Op.sub 13 2 2, Op.sub 15 2 2, Op.sub 16 2 2, Op.sub 18 2 2, Op.sub 19 2 2,
    Op.sub 20 2 2, Op.sub 21 2 2, Op.sub 22 2 2, Op.add 14 2 3, Op.add 17 2 3,
    Op.sub 24 2 3 ]

def upD : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 8
  | 3 => 9
  | 4 => 10
  | 5 => 13
  | 6 => 15
  | 7 => 16
  | 8 => 18
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 22
  | 13 => 14
  | 14 => 17
  | _ => 24

def upK (inp : ℕ) : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, mm => Function.update mm 1 (mm inp + mm 2)
  | 1, mm => Function.update mm 0 (mm 25 + mm 2)
  | 2, mm => Function.update mm 8 (mm 2 - mm 2)
  | 3, mm => Function.update mm 9 (mm 2 - mm 2)
  | 4, mm => Function.update mm 10 (mm 2 - mm 2)
  | 5, mm => Function.update mm 13 (mm 2 - mm 2)
  | 6, mm => Function.update mm 15 (mm 2 - mm 2)
  | 7, mm => Function.update mm 16 (mm 2 - mm 2)
  | 8, mm => Function.update mm 18 (mm 2 - mm 2)
  | 9, mm => Function.update mm 19 (mm 2 - mm 2)
  | 10, mm => Function.update mm 20 (mm 2 - mm 2)
  | 11, mm => Function.update mm 21 (mm 2 - mm 2)
  | 12, mm => Function.update mm 22 (mm 2 - mm 2)
  | 13, mm => Function.update mm 14 (mm 2 + mm 3)
  | 14, mm => Function.update mm 17 (mm 2 + mm 3)
  | _, mm => Function.update mm 24 (mm 2 - mm 3)

def mstep (inp : ℕ) : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, m => m
  | (k+1), m => upK inp k (mstep inp k m)

def mrest (inp : ℕ) : ℕ → ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | a, 0, mm => mm
  | a, (j+1), mm => upK inp (a + j) (mrest inp a j mm)

theorem upK_eq (inp k : ℕ) (hk : k < 16) (mm : ℕ → ℤ) :
    ∃ v : ℤ, upK inp k mm = Function.update mm (upD k) v := by
  interval_cases k <;> exact ⟨_, rfl⟩

theorem upK_frame (inp k : ℕ) (hk : k < 16) (mm : ℕ → ℤ) {i : ℕ} (hi : i ≠ upD k) :
    (upK inp k mm) i = mm i := by
  obtain ⟨v, hv⟩ := upK_eq inp k hk mm
  rw [hv]
  exact Function.update_of_ne hi v mm

theorem mstep_frame (inp : ℕ) (m : ℕ → ℤ) :
    ∀ k, k ≤ 16 → ∀ i, (∀ j, j < k → upD j ≠ i) → (mstep inp k m) i = m i := by
  intro k
  induction k with
  | zero => intro _ i _; rfl
  | succ k ih =>
    intro hk i hi
    show (upK inp k (mstep inp k m)) i = m i
    rw [upK_frame inp k (by omega) _ (Ne.symm (hi k (by omega)))]
    exact ih (by omega) i (fun j hj => hi j (by omega))

theorem mstep_compose (inp a b : ℕ) (m : ℕ → ℤ) :
    mstep inp (a+b) m = mrest inp a b (mstep inp a m) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b+1) = a + b + 1 by omega]
    show upK inp (a+b) (mstep inp (a+b) m) = mrest inp a (b+1) (mstep inp a m)
    rw [ih]
    rfl

theorem mrest_frame (inp a : ℕ) (mm : ℕ → ℤ) (b : ℕ) (hab : a + b ≤ 16) :
    ∀ i, (∀ j, j < b → upD (a+j) ≠ i) → (mrest inp a b mm) i = mm i := by
  induction b with
  | zero => intro i _; rfl
  | succ b ih =>
    intro i hi
    show (upK inp (a+b) (mrest inp a b mm)) i = mm i
    rw [upK_frame inp (a+b) (by omega) _ (Ne.symm (hi b (by omega)))]
    exact ih (by omega) i (fun j hj => hi j (by omega))

theorem mstep_last (inp : ℕ) (m : ℕ → ℤ) {k r : ℕ} (hk : k < 16) (hr : upD k = r)
    (hno : ∀ j, k + 1 ≤ j → j < 16 → upD j ≠ r) :
    (mstep inp 16 m) r = (upK inp k (mstep inp k m)) r := by
  have hcomp : mstep inp 16 m = mrest inp (k+1) (16 - (k+1)) (mstep inp (k+1) m) := by
    rw [← mstep_compose inp (k+1) (16-(k+1)) m]
    congr 1
    omega
  rw [hcomp]
  rw [mrest_frame inp (k+1) (mstep inp (k+1) m) (16-(k+1)) (by omega) r (by
    intro j hj
    exact hno (k+1+j) (by omega) (by omega))]
  rfl

theorem rprog_step (inp : ℕ) (k : ℕ) (hk : k < 16) (m : ℕ → ℤ) :
    stepP (rprog inp) ⟨k, mstep inp k m⟩ = ⟨k + 1, mstep inp (k+1) m⟩ := by
  interval_cases k <;>
    simp only [stepP, rprog, Op.exec, mstep, upK, List.getElem?_cons_zero, List.getElem?_cons_succ]

theorem rprog_run (inp : ℕ) (m : ℕ → ℤ) :
    Run (rprog inp) 16 ⟨0, m⟩ = ⟨16, mstep inp 16 m⟩ := by
  have h : ∀ k, k ≤ 16 → Run (rprog inp) k ⟨0, m⟩ = ⟨k, mstep inp k m⟩ := by
    intro k hk
    induction k with
    | zero => simp [mstep]
    | succ k ih => rw [Run_succ, ih (by omega), rprog_step inp k (by omega)]
  exact h 16 le_rfl

theorem rprog_spec (r q inp : ℕ) (hinp : 25 ≤ inp) (m : ℕ → ℤ)
    (h2 : m 2 = 0) (h3 : m 3 = 1) (h25 : m 25 = (r : ℤ)) (hinpv : m inp = (q : ℤ))
    (h4 : m 4 = 2) (h5 : m 5 = 3) (h6 : m 6 = 4) (h7 : m 7 = 5)
    (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0) :
    Run (rprog inp) 16 ⟨0, m⟩ = ⟨16, mstep inp 16 m⟩ ∧
    (∀ i, i ≤ 24 → (mstep inp 16 m) i = LinitMem r q i) ∧
    (∀ i, 25 ≤ i → (mstep inp 16 m) i = m i) := by
  have e1 : (mstep inp 16 m) 1 = m inp + m 2 := by
    rw [mstep_last inp m (k := 0) (r := 1) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 0 m) 1 ((mstep inp 0 m) inp + (mstep inp 0 m) 2)) 1 = m inp + m 2
    rw [Function.update_self]
    rfl
  have e0 : (mstep inp 16 m) 0 = m 25 + m 2 := by
    rw [mstep_last inp m (k := 1) (r := 0) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 1 m) 0 ((mstep inp 1 m) 25 + (mstep inp 1 m) 2)) 0 = m 25 + m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 1 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
    rw [mstep_frame inp m 1 (by omega) 25 (by intro j hj; interval_cases j <;> decide)]
  have e8 : (mstep inp 16 m) 8 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 2) (r := 8) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 2 m) 8 ((mstep inp 2 m) 2 - (mstep inp 2 m) 2)) 8 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 2 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e9 : (mstep inp 16 m) 9 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 3) (r := 9) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 3 m) 9 ((mstep inp 3 m) 2 - (mstep inp 3 m) 2)) 9 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 3 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e10 : (mstep inp 16 m) 10 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 4) (r := 10) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 4 m) 10 ((mstep inp 4 m) 2 - (mstep inp 4 m) 2)) 10 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 4 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e13 : (mstep inp 16 m) 13 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 5) (r := 13) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 5 m) 13 ((mstep inp 5 m) 2 - (mstep inp 5 m) 2)) 13 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 5 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e15 : (mstep inp 16 m) 15 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 6) (r := 15) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 6 m) 15 ((mstep inp 6 m) 2 - (mstep inp 6 m) 2)) 15 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 6 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e16 : (mstep inp 16 m) 16 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 7) (r := 16) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 7 m) 16 ((mstep inp 7 m) 2 - (mstep inp 7 m) 2)) 16 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 7 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e18 : (mstep inp 16 m) 18 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 8) (r := 18) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 8 m) 18 ((mstep inp 8 m) 2 - (mstep inp 8 m) 2)) 18 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 8 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e19 : (mstep inp 16 m) 19 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 9) (r := 19) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 9 m) 19 ((mstep inp 9 m) 2 - (mstep inp 9 m) 2)) 19 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 9 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e20 : (mstep inp 16 m) 20 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 10) (r := 20) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 10 m) 20 ((mstep inp 10 m) 2 - (mstep inp 10 m) 2)) 20 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 10 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e21 : (mstep inp 16 m) 21 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 11) (r := 21) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 11 m) 21 ((mstep inp 11 m) 2 - (mstep inp 11 m) 2)) 21 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 11 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e22 : (mstep inp 16 m) 22 = m 2 - m 2 := by
    rw [mstep_last inp m (k := 12) (r := 22) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 12 m) 22 ((mstep inp 12 m) 2 - (mstep inp 12 m) 2)) 22 = m 2 - m 2
    rw [Function.update_self]
    rw [mstep_frame inp m 12 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
  have e14 : (mstep inp 16 m) 14 = m 2 + m 3 := by
    rw [mstep_last inp m (k := 13) (r := 14) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 13 m) 14 ((mstep inp 13 m) 2 + (mstep inp 13 m) 3)) 14 = m 2 + m 3
    rw [Function.update_self]
    rw [mstep_frame inp m 13 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
    rw [mstep_frame inp m 13 (by omega) 3 (by intro j hj; interval_cases j <;> decide)]
  have e17 : (mstep inp 16 m) 17 = m 2 + m 3 := by
    rw [mstep_last inp m (k := 14) (r := 17) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 14 m) 17 ((mstep inp 14 m) 2 + (mstep inp 14 m) 3)) 17 = m 2 + m 3
    rw [Function.update_self]
    rw [mstep_frame inp m 14 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
    rw [mstep_frame inp m 14 (by omega) 3 (by intro j hj; interval_cases j <;> decide)]
  have e24 : (mstep inp 16 m) 24 = m 2 - m 3 := by
    rw [mstep_last inp m (k := 15) (r := 24) (by omega) rfl (by intro j hj h16; interval_cases j <;> decide)]
    show (Function.update (mstep inp 15 m) 24 ((mstep inp 15 m) 2 - (mstep inp 15 m) 3)) 24 = m 2 - m 3
    rw [Function.update_self]
    rw [mstep_frame inp m 15 (by omega) 2 (by intro j hj; interval_cases j <;> decide)]
    rw [mstep_frame inp m 15 (by omega) 3 (by intro j hj; interval_cases j <;> decide)]
  refine ⟨rprog_run inp m, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · rw [e0, h2, h25]; simp [LinitMem]
    · rw [e1, h2, hinpv]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 2 (by intro j hj; interval_cases j <;> decide), h2]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 3 (by intro j hj; interval_cases j <;> decide), h3]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 4 (by intro j hj; interval_cases j <;> decide), h4]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 5 (by intro j hj; interval_cases j <;> decide), h5]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 6 (by intro j hj; interval_cases j <;> decide), h6]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 7 (by intro j hj; interval_cases j <;> decide), h7]; simp [LinitMem]
    · rw [e8, h2]; simp [LinitMem]
    · rw [e9, h2]; simp [LinitMem]
    · rw [e10, h2]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 11 (by intro j hj; interval_cases j <;> decide), h11]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 12 (by intro j hj; interval_cases j <;> decide), h12]; simp [LinitMem]
    · rw [e13, h2]; simp [LinitMem]
    · rw [e14, h2, h3]; simp [LinitMem]
    · rw [e15, h2]; simp [LinitMem]
    · rw [e16, h2]; simp [LinitMem]
    · rw [e17, h2, h3]; simp [LinitMem]
    · rw [e18, h2]; simp [LinitMem]
    · rw [e19, h2]; simp [LinitMem]
    · rw [e20, h2]; simp [LinitMem]
    · rw [e21, h2]; simp [LinitMem]
    · rw [e22, h2]; simp [LinitMem]
    · rw [mstep_frame inp m 16 (by omega) 23 (by intro j hj; interval_cases j <;> decide), h23]; simp [LinitMem]
    · rw [e24, h2, h3]; simp [LinitMem]
  · intro i hi
    have h : ∀ j, j < 16 → upD j ≠ i := by
      intro j hj
      have hle : upD j ≤ 24 := by interval_cases j <;> decide
      omega
    exact mstep_frame inp m 16 (by omega) i h

def OpLeOr (P : ℕ → Prop) : Op → Prop
  | .add d _ _ => P d
  | .sub d _ _ => P d
  | .mul d _ _ => P d
  | .quo d _ _ => P d
  | .rem d _ _ => P d
  | .load d _ => P d
  | .store _ _ => False
  | .jgt _ _ _ => True
  | .jeq _ _ _ => True
  | .jmp _ => True
  | .halt => True

theorem OpLeOr.mem_frame {P : ℕ → Prop} {op : Op} (h : OpLeOr P op) {s : State} {i : ℕ}
    (hi : ¬ P i) : (op.exec s).mem i = s.mem i := by
  match op with
  | .add d a b | .sub d a b | .mul d a b | .quo d a b | .rem d a b | .load d a =>
    rw [Op.exec]
    exact Function.update_of_ne (by intro hc; exact hi (hc ▸ h)) _ _
  | .store a b => exact h.elim
  | .jgt a b L => rfl
  | .jeq a b L => rfl
  | .jmp L => rfl
  | .halt => rfl

theorem Run_frame (Pp : List Op) (P : ℕ → Prop) (h : ∀ op ∈ Pp, OpLeOr P op) (s : State) :
    ∀ t, ∀ i, ¬ P i → (Run Pp t s).mem i = s.mem i := by
  intro t
  induction t generalizing s with
  | zero => intro i _; rfl
  | succ t ih =>
    intro i hi
    rw [Run_succ]
    cases hop : Pp[(Run Pp t s).pc]? with
    | none => simp only [stepP, hop]; exact ih s i hi
    | some op =>
      have hmem : op ∈ Pp := by rw [List.mem_iff_getElem?]; exact ⟨_, hop⟩
      simp only [stepP, hop]
      rw [OpLeOr.mem_frame (h op hmem) hi]
      exact ih s i hi

theorem OpLeOr_shiftOp {P : ℕ → Prop} {off : ℕ} {op : Op} (h : OpLeOr P op) :
    OpLeOr P (shiftOp off op) := by
  match op with
  | .add d a b => exact h
  | .sub d a b => exact h
  | .mul d a b => exact h
  | .quo d a b => exact h
  | .rem d a b => exact h
  | .load d a => exact h
  | .store a b => exact h
  | .jgt a b L => trivial
  | .jeq a b L => trivial
  | .jmp L => trivial
  | .halt => trivial

def OpNoStore : Op → Prop
  | .store _ _ => False
  | _ => True

instance decOpNoStore (op : Op) : Decidable (OpNoStore op) := by
  cases op <;> (simp only [OpNoStore] <;> infer_instance)

theorem OpSmall_le {N : ℕ} {op : Op} (h : OpSmall N op) (hns : OpNoStore op) :
    OpLeOr (fun d => d ≤ N) op := by
  match op with
  | .add d a b | .sub d a b | .mul d a b | .quo d a b | .rem d a b => exact h.1
  | .load d a => exact h.elim
  | .store a b => exact hns.elim
  | .jgt a b L => trivial
  | .jeq a b L => trivial
  | .jmp L => trivial
  | .halt => trivial

theorem Lprog_nostore : ∀ op ∈ Lprog, OpNoStore op := by decide

theorem Lprog_le24 : ∀ op ∈ Lprog, OpLeOr (fun d => d ≤ 24) op :=
  fun op h => OpSmall_le (Lprog_small op h) (Lprog_nostore op h)

theorem OpLeOr_mono {P Q : ℕ → Prop} {op : Op} (h : OpLeOr P op) (hPQ : ∀ d, P d → Q d) :
    OpLeOr Q op := by
  match op with
  | .add d a b | .sub d a b | .mul d a b | .quo d a b | .rem d a b | .load d a => exact hPQ d h
  | .store a b => exact h
  | .jgt a b L => trivial
  | .jeq a b L => trivial
  | .jmp L => trivial
  | .halt => trivial

theorem rprog_le24 (inp : ℕ) : ∀ op ∈ rprog inp, OpLeOr (fun d => d ≤ 24) op := by
  intro op hop
  simp only [rprog, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (simp only [OpLeOr])
  all_goals (try omega)
  all_goals trivial

theorem Ltail_ops (out : ℕ) : ∀ op ∈ Ltail out, OpLeOr (fun d => d ≤ 24 ∨ d = out) op := by
  intro op hop
  rw [Ltail] at hop
  rcases List.mem_append.mp hop with h | h
  · exact OpLeOr_mono (Lprog_le24 op (List.mem_of_mem_take h)) (fun d hd => Or.inl hd)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact Or.inr rfl

theorem shiftProg_ops {P : ℕ → Prop} {off : ℕ} {Q : List Op} (h : ∀ op ∈ Q, OpLeOr P op) :
    ∀ op ∈ shiftProg off Q, OpLeOr P op := by
  intro op hop
  rw [shiftProg, List.mem_map] at hop
  obtain ⟨op', hop', rfl⟩ := hop
  exact OpLeOr_shiftOp (h op' hop')

def blk (inp out : ℕ) : List Op := rprog inp ++ shiftProg 16 (Ltail out)

theorem rprog_length (inp : ℕ) : (rprog inp).length = 16 := rfl

theorem blk_length (inp out : ℕ) : (blk inp out).length = 65 := by
  simp [blk, rprog_length, shiftProg_length, Ltail_length]

theorem blk_ops (inp out : ℕ) : ∀ op ∈ blk inp out, OpLeOr (fun d => d ≤ 24 ∨ d = out) op := by
  intro op hop
  rw [blk] at hop
  rcases List.mem_append.mp hop with h | h
  · exact OpLeOr_mono (rprog_le24 inp op h) (fun d hd => Or.inl hd)
  · exact shiftProg_ops (Ltail_ops out) op h



theorem Run_stuck_none (Pp : List Op) (s : State) (h : Pp[s.pc]? = none) :
    ∀ t, Run Pp t s = s := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [Run_succ, ih]; simp only [stepP, h]

theorem Run_Lprog (t : ℕ) (s : State) : Run Lprog t s = Lrun t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => rw [Run_succ, ih, Lrun_succ]; rfl

def LogSpec (r q : ℕ) (o : ℤ) : Prop :=
  (∃ a : ℕ, a < 2^(r-2) ∧ ((q : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r))^a ∧ o = (a : ℤ)) ∨
  (o = -1 ∧ ∀ a : ℕ, a < 2^(r-2) → ((q : ℤ) : ZMod (2^r)) ≠ (5 : ZMod (2^r))^a)

theorem Ltail_step47 (out : ℕ) (mm : ℕ → ℤ) :
    Run (Ltail out) 1 (⟨47, mm⟩ : State)
      = ⟨48, Function.update mm out (mm 24 + mm 2)⟩ := by
  rw [show (1:ℕ) = 0+1 from rfl, Run_succ, Run_zero]
  show (match (Ltail out)[47]? with
    | some op => op.exec ⟨47, mm⟩
    | none => (⟨47, mm⟩ : State)) = _
  rw [Ltail_getElem?_47]
  rfl

theorem Ltail_step48 (out : ℕ) (mm : ℕ → ℤ) :
    Run (Ltail out) 1 (⟨48, mm⟩ : State)
      = ⟨49, Function.update mm out (mm 24 + mm 2)⟩ := by
  rw [show (1:ℕ) = 0+1 from rfl, Run_succ, Run_zero]
  show (match (Ltail out)[48]? with
    | some op => op.exec ⟨48, mm⟩
    | none => (⟨48, mm⟩ : State)) = _
  rw [Ltail_getElem?_48]
  rfl

theorem Ltail_getElem?_49 (out : ℕ) : (Ltail out)[49]? = none := by
  rw [← Ltail_length out]
  exact List.getElem?_length _

theorem Ltail_step49 (out : ℕ) (mm : ℕ → ℤ) :
    Run (Ltail out) 1 (⟨49, mm⟩ : State) = ⟨49, mm⟩ := by
  rw [show (1:ℕ) = 0+1 from rfl, Run_succ, Run_zero]
  show (match (Ltail out)[49]? with
    | some op => op.exec ⟨49, mm⟩
    | none => (⟨49, mm⟩ : State)) = _
  rw [Ltail_getElem?_49]

theorem rprog_run_le (inp : ℕ) (m : ℕ → ℤ) :
    ∀ t ≤ 16, Run (rprog inp) t ⟨0, m⟩ = ⟨t, mstep inp t m⟩ := by
  intro t ht
  induction t with
  | zero => simp [mstep]
  | succ t ih => rw [Run_succ, ih (by omega), rprog_step inp t (by omega)]

theorem rprog_pc (inp : ℕ) (m : ℕ → ℤ) : ∀ t ≤ 16, (Run (rprog inp) t ⟨0, m⟩).pc = t :=
  fun t ht => congrArg State.pc (rprog_run_le inp m t ht)

theorem blk_spec (r q : ℕ) (hr : 3 ≤ r) (hodd : Odd q) (hq1 : 1 ≤ q) (hqu : q < 2^r)
    (inp out : ℕ) (hinp : 25 ≤ inp) (hout : 25 ≤ out)
    (m : ℕ → ℤ) (h25 : m 25 = (r : ℤ)) (hinpv : m inp = (q : ℤ))
    (h2 : m 2 = 0) (h3 : m 3 = 1) (h4 : m 4 = 2) (h5 : m 5 = 3) (h6 : m 6 = 4)
    (h7 : m 7 = 5) (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0) :
    ∃ T1, T1 ≤ 18 + (40*(r+1)*(r+1)+100) ∧ ∃ m2 : ℕ → ℤ,
      Run (blk inp out) T1 ⟨0, m⟩ = ⟨65, m2⟩ ∧
      (∀ t < T1, (Run (blk inp out) t ⟨0, m⟩).pc < 65) ∧
      LogSpec r q (m2 out) ∧
      (∀ i, 25 ≤ i → i ≠ out → m2 i = m i) ∧
      (∀ i, i ∈ ({2,3,4,5,6,7,11,12,23} : Finset ℕ) → m2 i = m i) := by
  obtain ⟨hres, hagree, hfr⟩ := rprog_spec r q inp hinp m h2 h3 h25 hinpv h4 h5 h6 h7 h11 h12 h23
  obtain ⟨TL, hTL, hpre, hlog⟩ := lt_log r q hr hodd hq1 hqu
  have hmul2 : (mstep inp 16 m) 2 = 0 := by rw [hagree 2 (by omega)]; simp [LinitMem]
  have hres16 : Run (blk inp out) 16 ⟨0, m⟩ = ⟨16, mstep inp 16 m⟩ := by
    rw [blk]
    rw [Run_prefix (rprog inp) (shiftProg 16 (Ltail out)) 16 ⟨0, m⟩
      (by intro t ht; rw [rprog_pc inp m t (by omega)]; rw [rprog_length]; omega) 16 le_rfl]
    exact hres
  have hpreL : ∀ t < TL, (Run Lprog t (⟨0, mstep inp 16 m⟩ : State)).pc < 47 := by
    intro t ht
    have h2' := (Lrun_agree t 0 (mstep inp 16 m) (LinitMem r q) hagree).1
    have h3' : (Lrun t ⟨0, mstep inp 16 m⟩).pc = (Lrun t (Ls0 r q)).pc := by simpa [Ls0] using h2'
    have h4' : (Run Lprog t (⟨0, mstep inp 16 m⟩ : State)).pc = (Lrun t ⟨0, mstep inp 16 m⟩).pc :=
      congrArg State.pc (Run_Lprog t _)
    have h5' := hpre t ht
    omega
  have hpref : ∀ t ≤ TL, Run (Ltail out) t (⟨0, mstep inp 16 m⟩ : State)
      = Lrun t (⟨0, mstep inp 16 m⟩ : State) := by
    intro t ht
    rw [Run_prefix_eq Lprog (Ltail out) 47 TL ⟨0, mstep inp 16 m⟩
      (fun i hi => Ltail_getElem?_lt out i hi) hpreL t ht, Run_Lprog]
  have haTL : ∀ i, i ≤ 24 → (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).mem i
      = (Lrun TL (Ls0 r q)).mem i := by
    intro i hi
    rw [hpref TL le_rfl]
    simpa [Ls0] using (Lrun_agree TL 0 (mstep inp 16 m) (LinitMem r q) hagree).2 i hi
  have hpTL : (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).pc = (Lrun TL (Ls0 r q)).pc := by
    rw [hpref TL le_rfl]
    simpa [Ls0] using (Lrun_agree TL 0 (mstep inp 16 m) (LinitMem r q) hagree).1
  have hm24 : (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).mem 24 = (Lrun TL (Ls0 r q)).mem 24 :=
    haTL 24 (by omega)
  have hm2L : (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).mem 2 = 0 := by
    rw [haTL 2 (by omega), (Lrun_consts r q TL).1]
    simp [LinitMem]
  have hTLstate : Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)
      = (⟨(Lrun TL (Ls0 r q)).pc,
          (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).mem⟩ : State) :=
    state_pc_eq hpTL
  -- the two tail steps yield the final tail memory
  set mm : ℕ → ℤ := (Run (Ltail out) TL (⟨0, mstep inp 16 m⟩ : State)).mem with hmm_def
  have hmm_frame : ∀ i, 25 ≤ i → i ≠ out → mm i = mstep inp 16 m i := by
    intro i hi hio
    exact Run_frame (Ltail out) (fun d => d ≤ 24 ∨ d = out) (Ltail_ops out) _ TL i
      (by rintro (h1 | h2) <;> omega)
  obtain ⟨mfin, hfin_eq, hfin_out, hfin_pre, hfin_frame⟩ :
      ∃ mfin : ℕ → ℤ,
        Run (Ltail out) (TL+2) (⟨0, mstep inp 16 m⟩ : State) = ⟨49, mfin⟩ ∧
        mfin out = (Lrun TL (Ls0 r q)).mem 24 ∧
        (∀ i, i ≤ 24 → mfin i = mm i) ∧
        (∀ i, 25 ≤ i → i ≠ out → mfin i = m i) := by
    rcases hlog with ⟨h47, a, ha, hq5, h24⟩ | ⟨h48, h24, hne⟩
    · have h1 : Run (Ltail out) (TL+1) (⟨0, mstep inp 16 m⟩ : State)
          = ⟨48, Function.update mm out (mm 24 + mm 2)⟩ := by
        rw [show TL+1 = TL+1 from rfl, Run_add, hTLstate, h47]
        exact Ltail_step47 out mm
      refine ⟨Function.update (Function.update mm out (mm 24 + mm 2)) out
        ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2),
        ?_, ?_, ?_, ?_⟩
      · rw [show TL+2 = (TL+1)+1 from rfl, Run_add, h1, Ltail_step48 out _]
      · show Function.update (Function.update mm out (mm 24 + mm 2)) out
            ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2) out
          = (Lrun TL (Ls0 r q)).mem 24
        rw [Function.update_self, Function.update_of_ne (by omega : (24:ℕ) ≠ out),
            Function.update_of_ne (by omega : (2:ℕ) ≠ out), hm24, hm2L]
        ring
      · intro i hi
        show Function.update (Function.update mm out (mm 24 + mm 2)) out
            ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2) i = mm i
        rw [Function.update_of_ne (by omega : i ≠ out), Function.update_of_ne (by omega : i ≠ out)]
      · intro i hi hio
        show Function.update (Function.update mm out (mm 24 + mm 2)) out
            ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2) i = m i
        rw [Function.update_of_ne (by omega : i ≠ out), Function.update_of_ne (by omega : i ≠ out),
            hmm_frame i hi hio, hfr i hi]
    · have h1 : Run (Ltail out) (TL+1) (⟨0, mstep inp 16 m⟩ : State)
          = ⟨49, Function.update mm out (mm 24 + mm 2)⟩ := by
        rw [show TL+1 = TL+1 from rfl, Run_add, hTLstate, h48]
        exact Ltail_step48 out mm
      refine ⟨Function.update mm out (mm 24 + mm 2), ?_, ?_, ?_, ?_⟩
      · rw [show TL+2 = (TL+1)+1 from rfl, Run_add, h1, Ltail_step49 out _]
      · show (Function.update mm out (mm 24 + mm 2)) out = (Lrun TL (Ls0 r q)).mem 24
        rw [Function.update_self, hm24, hm2L]; ring
      · intro i hi
        show (Function.update mm out (mm 24 + mm 2)) i = mm i
        rw [Function.update_of_ne (by omega : i ≠ out)]
      · intro i hi hio
        show (Function.update mm out (mm 24 + mm 2)) i = m i
        rw [Function.update_of_ne (by omega : i ≠ out), hmm_frame i hi hio, hfr i hi]
  have hbstate : Run (blk inp out) (16 + (TL+2)) ⟨0, m⟩ = ⟨65, mfin⟩ := by
    rw [show 16 + (TL+2) = 16 + (TL+2) from rfl, Run_add, hres16, blk]
    have happ := Run_append_shift (rprog inp) (Ltail out) (TL+2) 0 (mstep inp 16 m)
    rw [rprog_length inp, show (16:ℕ) + 0 = 16 from rfl] at happ
    rw [happ, hfin_eq]
    norm_num
  have hex : ∃ t, (Run (blk inp out) t ⟨0, m⟩).pc = 65 := ⟨16 + (TL+2), by rw [hbstate]⟩
  have hbound : Nat.find hex ≤ 16 + (TL+2) := by
    have := Nat.find_min' hex (show (Run (blk inp out) (16 + (TL+2)) ⟨0, m⟩).pc = 65 by rw [hbstate])
    omega
  have hple : ∀ t ≤ 16 + (TL+2), (Run (blk inp out) t ⟨0, m⟩).pc ≤ 65 := by
    intro t ht
    by_contra hc
    have hnone : (blk inp out)[(Run (blk inp out) t ⟨0, m⟩).pc]? = none := by
      rw [List.getElem?_eq_none_iff, blk_length]; omega
    have hstuck : Run (blk inp out) (16 + (TL+2)) ⟨0, m⟩ = Run (blk inp out) t ⟨0, m⟩ := by
      rw [show 16 + (TL+2) = t + (16 + (TL+2) - t) by omega]
      rw [Run_add]
      exact Run_stuck_none (blk inp out) _ hnone (16 + (TL+2) - t)
    rw [hbstate] at hstuck
    have hpc : (65:ℕ) = (Run (blk inp out) t ⟨0, m⟩).pc := congrArg State.pc hstuck
    omega
  refine ⟨Nat.find hex, ?_, mfin, ?_, ?_, ?_, ?_, ?_⟩
  · have := Nat.find_min' hex (show (Run (blk inp out) (16 + (TL+2)) ⟨0, m⟩).pc = 65 by rw [hbstate])
    omega
  · have hspec := Nat.find_spec hex
    have hnone : (blk inp out)[65]? = none := by
      rw [List.getElem?_eq_none_iff, blk_length]
    have hst : ∀ t', Run (blk inp out) t' (Run (blk inp out) (Nat.find hex) ⟨0, m⟩)
        = Run (blk inp out) (Nat.find hex) ⟨0, m⟩ :=
      Run_stuck_none (blk inp out) _ (by rw [hspec]; exact hnone)
    have heq : Run (blk inp out) (16 + (TL+2)) ⟨0, m⟩ = Run (blk inp out) (Nat.find hex) ⟨0, m⟩ := by
      rw [show 16 + (TL+2) = Nat.find hex + ((16 + (TL+2)) - Nat.find hex) by omega, Run_add, hst]
    rw [← heq]; exact hbstate
  · intro t ht
    have hne : (Run (blk inp out) t ⟨0, m⟩).pc ≠ 65 := fun hc => Nat.find_min hex ht hc
    have hle : (Run (blk inp out) t ⟨0, m⟩).pc ≤ 65 := hple t (by omega)
    omega
  · rcases hlog with ⟨h47, a, ha, hq5, h24⟩ | ⟨h48, h24, hne⟩
    · refine Or.inl ⟨a, ha, hq5, ?_⟩
      rw [hfin_out, h24]
    · refine Or.inr ⟨?_, hne⟩
      rw [hfin_out, h24]
  · intro i hi hio
    exact hfin_frame i hi hio
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hfin_pre 2 (by omega), haTL 2 (by omega), (Lrun_consts r q TL).1, h2]
      simp [LinitMem]
    · rw [hfin_pre 3 (by omega), haTL 3 (by omega), (Lrun_consts r q TL).2.1, h3]
      simp [LinitMem]
    · rw [hfin_pre 4 (by omega), haTL 4 (by omega), (Lrun_consts r q TL).2.2.1, h4]
      simp [LinitMem]
    · rw [hfin_pre 5 (by omega), haTL 5 (by omega), (Lrun_consts r q TL).2.2.2.1, h5]
      simp [LinitMem]
    · rw [hfin_pre 6 (by omega), haTL 6 (by omega), (Lrun_consts r q TL).2.2.2.2.1, h6]
      simp [LinitMem]
    · rw [hfin_pre 7 (by omega), haTL 7 (by omega), (Lrun_consts r q TL).2.2.2.2.2.1, h7]
      simp [LinitMem]
    · rw [hfin_pre 11 (by omega), haTL 11 (by omega), (Lrun_consts r q TL).2.2.2.2.2.2.1, h11]
      simp [LinitMem]
    · rw [hfin_pre 12 (by omega), haTL 12 (by omega), (Lrun_consts r q TL).2.2.2.2.2.2.2.1, h12]
      simp [LinitMem]
    · rw [hfin_pre 23 (by omega), haTL 23 (by omega), (Lrun_consts r q TL).2.2.2.2.2.2.2.2, h23]
      simp [LinitMem]

end BkSet.RAM

namespace BkSet.RAM
open Nat

def Nprog : List (ℕ × ℕ) → List Op
  | [] => []
  | (i, o) :: rest => blk i o ++ shiftProg (blk i o).length (Nprog rest)

theorem Nprog_length : ∀ L : List (ℕ × ℕ), (Nprog L).length = 65 * L.length
  | [] => rfl
  | (i, o) :: rest => by
      rw [Nprog, List.length_append, shiftProg_length, blk_length, Nprog_length rest,
        List.length_cons]
      ring

theorem Nprog_spec (r : ℕ) (hr : 3 ≤ r) (L : List (ℕ × ℕ)) (m : ℕ → ℤ)
    (h25 : m 25 = (r : ℤ)) (h2 : m 2 = 0) (h3 : m 3 = 1) (h4 : m 4 = 2) (h5 : m 5 = 3)
    (h6 : m 6 = 4) (h7 : m 7 = 5) (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0)
    (hpre : ∀ p ∈ L, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25)
    (hnd : L.Nodup)
    (hdisj : ∀ p ∈ L, ∀ p' ∈ L, p.1 ≠ p'.2)
    (hdisj2 : ∀ p ∈ L, ∀ p' ∈ L, p ≠ p' → p.2 ≠ p'.2)
    (hval : ∀ p ∈ L, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m p.1 = (q : ℤ)) :
    ∃ T, T ≤ L.length * (18 + (40*(r+1)*(r+1)+100)) ∧ ∃ m' : ℕ → ℤ,
      Run (Nprog L) T ⟨0, m⟩ = ⟨(Nprog L).length, m'⟩ ∧
      (∀ p ∈ L, ∀ q : ℕ, Odd q → 1 ≤ q → q < 2^r → m p.1 = (q : ℤ) → LogSpec r q (m' p.2)) ∧
      (∀ i, 25 ≤ i → (∀ p ∈ L, i ≠ p.2) → m' i = m i) ∧
      (m' 2 = 0 ∧ m' 3 = 1 ∧ m' 4 = 2 ∧ m' 5 = 3 ∧ m' 6 = 4 ∧ m' 7 = 5 ∧ m' 11 = 0 ∧
        m' 12 = 0 ∧ m' 23 = 0) := by
  induction L generalizing m with
  | nil =>
    refine ⟨0, by simp, m, ?_, ?_, ?_, ?_⟩
    · simp [Nprog]
    · intro p hp; simp at hp
    · intro i hi _; rfl
    · exact ⟨h2, h3, h4, h5, h6, h7, h11, h12, h23⟩
  | cons p rest ih =>
    obtain ⟨i, o⟩ := p
    obtain ⟨hp1, hp2, hp3⟩ := hpre (i, o) (by simp)
    obtain ⟨q, hqodd, hq1, hqu, hqv⟩ := hval (i, o) (by simp)
    obtain ⟨T1, hT1, m1, hrun1, hpto1, hlog1, hframe1, hconst1⟩ :=
      blk_spec r q hr hqodd hq1 hqu i o hp1 hp2 m h25 hqv h2 h3 h4 h5 h6 h7 h11 h12 h23
    -- hypotheses for the rest
    have hpre' : ∀ p ∈ rest, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25 := fun p hp => hpre p (by simp only [List.mem_cons]; exact Or.inr hp)
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : (i, o) ∉ rest := (List.nodup_cons.mp hnd).1
    have hdisj' : ∀ p ∈ rest, ∀ p' ∈ rest, p.1 ≠ p'.2 := fun p hp p' hp' => hdisj p (by simp only [List.mem_cons]; exact Or.inr hp) p' (by simp only [List.mem_cons]; exact Or.inr hp')
    have hdisj2' : ∀ p ∈ rest, ∀ p' ∈ rest, p ≠ p' → p.2 ≠ p'.2 :=
      fun p hp p' hp' hne => hdisj2 p (by simp only [List.mem_cons]; exact Or.inr hp) p' (by simp only [List.mem_cons]; exact Or.inr hp') hne
    have hval' : ∀ p ∈ rest, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m1 p.1 = (q : ℤ) := by
      intro p hp
      obtain ⟨q', ho, h1, hu, hv⟩ := hval p (by simp only [List.mem_cons]; exact Or.inr hp)
      refine ⟨q', ho, h1, hu, ?_⟩
      rw [← hv]
      exact hframe1 p.1 (hpre p (by simp only [List.mem_cons]; exact Or.inr hp)).1
        (hdisj p (by simp only [List.mem_cons]; exact Or.inr hp) (i, o) (by simp))
    obtain ⟨T2, hT2, m2, hrun2, hlog2, hframe2, hconst2⟩ :=
      ih m1 (by rw [hframe1 25 (by omega) hp3.symm]; exact h25)
        (by rw [hconst1 2 (by decide)]; exact h2)
        (by rw [hconst1 3 (by decide)]; exact h3)
        (by rw [hconst1 4 (by decide)]; exact h4)
        (by rw [hconst1 5 (by decide)]; exact h5)
        (by rw [hconst1 6 (by decide)]; exact h6)
        (by rw [hconst1 7 (by decide)]; exact h7)
        (by rw [hconst1 11 (by decide)]; exact h11)
        (by rw [hconst1 12 (by decide)]; exact h12)
        (by rw [hconst1 23 (by decide)]; exact h23)
        hpre' hnd' hdisj' hdisj2' hval'
    -- combine
    refine ⟨T1 + T2, ?_, m2, ?_, ?_, ?_, ?_⟩
    · rw [show ((i, o) :: rest).length = rest.length + 1 from rfl]
      rw [show (rest.length + 1) * (18 + (40*(r+1)*(r+1)+100))
          = (18 + (40*(r+1)*(r+1)+100)) + rest.length * (18 + (40*(r+1)*(r+1)+100)) by ring]
      exact Nat.add_le_add hT1 hT2
    · rw [Nprog]
      rw [Run_concat (blk i o) (Nprog rest) T1 T2 ⟨0, m⟩
        (by intro t ht; rw [blk_length]; exact hpto1 t ht)
        (by rw [hrun1]; rw [blk_length])]
      rw [hrun1, hrun2, List.length_append, blk_length, shiftProg_length]
    · intro pp hpp q' ho h1 hu hv
      rcases List.mem_cons.mp hpp with rfl | hmem
      · have hqq : q = q' := by
          have hq2 : (q : ℤ) = (q' : ℤ) := by rw [← hqv, hv]
          exact_mod_cast hq2
        subst hqq
        have hmo : m2 o = m1 o :=
          hframe2 o (by omega)         (fun p hp => hdisj2 (i, o) (by simp) p (by simp only [List.mem_cons]; exact Or.inr hp)
          (by intro hc; exact hnot (hc ▸ hp)))
        rw [hmo]
        exact hlog1
      · refine hlog2 pp hmem q' ho h1 hu ?_
        rw [← hv]
        exact hframe1 pp.1 (hpre pp (by simp only [List.mem_cons]; exact Or.inr hmem)).1
          (hdisj pp (by simp only [List.mem_cons]; exact Or.inr hmem) (i, o) (by simp))
    · intro i' hi' hout
      rw [hframe2 i' hi' (fun p hp => hout p (by simp only [List.mem_cons]; exact Or.inr hp)),
          hframe1 i' hi' (by intro hc; exact hout (i, o) (by simp) (by simp [hc]))]
    · exact ⟨by simp [hconst2.1, hconst1 2 (by decide), h2],
        by simp [hconst2.2.1, hconst1 3 (by decide), h3],
        by simp [hconst2.2.2.1, hconst1 4 (by decide), h4],
        by simp [hconst2.2.2.2.1, hconst1 5 (by decide), h5],
        by simp [hconst2.2.2.2.2.1, hconst1 6 (by decide), h6],
        by simp [hconst2.2.2.2.2.2.1, hconst1 7 (by decide), h7],
        by simp [hconst2.2.2.2.2.2.2.1, hconst1 11 (by decide), h11],
        by simp [hconst2.2.2.2.2.2.2.2.1, hconst1 12 (by decide), h12],
        by simp [hconst2.2.2.2.2.2.2.2.2, hconst1 23 (by decide), h23]⟩ <;>
        (rw [hconst2.2.1, hconst1 _ (by decide), h3] <;> rfl) <;>
        (rw [hconst2.2.2.1, hconst1 _ (by decide), h4] <;> rfl) <;>
        (rw [hconst2.2.2.2.1, hconst1 _ (by decide), h5] <;> rfl) <;>
        (rw [hconst2.2.2.2.2.1, hconst1 _ (by decide), h6] <;> rfl) <;>
        (rw [hconst2.2.2.2.2.2.1, hconst1 _ (by decide), h7] <;> rfl) <;>
        (rw [hconst2.2.2.2.2.2.2.1, hconst1 _ (by decide), h11] <;> rfl) <;>
        (rw [hconst2.2.2.2.2.2.2.2.1, hconst1 _ (by decide), h12] <;> rfl) <;>
        (rw [hconst2.2.2.2.2.2.2.2.2, hconst1 _ (by decide), h23] <;> rfl)

end BkSet.RAM

namespace BkSet.RAM
open Nat

/-- **Lemma 1, `N`-fold form.**  Given a list `L` of (input register, output register) pairs,
the merged program `Nprog L` computes, for every pair `(inp, out) ∈ L`, the discrete logarithm
of the odd number `mem inp ∈ [1, 2^r)` modulo `2^r` into `mem out` (and `-1` when the input is
not in `⟨5⟩`), in at most `L.length * (18 + 40*(r+1)^2 + 100)` steps, while preserving every
register other than the outputs.  This is the "compute `N` discrete logarithms in the same
group" generalisation of Lemma 1. -/
theorem lemma1_N (r : ℕ) (hr : 3 ≤ r) (L : List (ℕ × ℕ))
    (hpre : ∀ p ∈ L, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25) (hnd : L.Nodup)
    (hdisj : ∀ p ∈ L, ∀ p' ∈ L, p.1 ≠ p'.2)
    (hdisj2 : ∀ p ∈ L, ∀ p' ∈ L, p ≠ p' → p.2 ≠ p'.2)
    (m : ℕ → ℤ) (h25 : m 25 = (r : ℤ)) (h2 : m 2 = 0) (h3 : m 3 = 1) (h4 : m 4 = 2)
    (h5 : m 5 = 3) (h6 : m 6 = 4) (h7 : m 7 = 5) (h11 : m 11 = 0) (h12 : m 12 = 0)
    (h23 : m 23 = 0)
    (hval : ∀ p ∈ L, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m p.1 = (q : ℤ)) :
    ∃ T, T ≤ L.length * (18 + (40*(r+1)*(r+1)+100)) ∧ ∃ m' : ℕ → ℤ,
      Run (Nprog L) T ⟨0, m⟩ = ⟨(Nprog L).length, m'⟩ ∧
      (∀ p ∈ L, ∀ q : ℕ, Odd q → 1 ≤ q → q < 2^r → m p.1 = (q : ℤ) →
        LogSpec r q (m' p.2)) ∧
      (∀ i, 25 ≤ i → (∀ p ∈ L, i ≠ p.2) → m' i = m i) := by
  obtain ⟨T, hT, m', h1, h2', h3', _⟩ :=
    Nprog_spec r hr L m h25 h2 h3 h4 h5 h6 h7 h11 h12 h23 hpre hnd hdisj hdisj2 hval
  exact ⟨T, hT, m', h1, h2', h3'⟩

end BkSet.RAM

namespace BkSet.RAM
open Nat

/-- **Merging a program with the `N`-fold logarithm routine.**  If `first` (an arbitrary
instruction list, e.g. a prime generator followed by a small setup) runs from `⟨0, m⟩` to
`⟨first.length, m1⟩` in `T1` steps while staying strictly below `first.length` before that, and
`m1` satisfies the constants and carries odd inputs in the registers listed by `inp`, then the
merged program `first ++ shiftProg first.length (Nprog inp)` computes all the logarithms of
`inp` in `T1 + |inp| * (18 + O(r^2))` steps.  This is the "two programs can be merged, and the
bounds add" step of Theorem 1. -/
theorem merge_prog (r : ℕ) (hr : 3 ≤ r) (first : List Op) (inp : List (ℕ × ℕ))
    (T1 : ℕ) (m m1 m' : ℕ → ℤ)
    (hfirst : Run first T1 ⟨0, m⟩ = ⟨first.length, m1⟩)
    (hpc : ∀ t < T1, (Run first t ⟨0, m⟩).pc < first.length)
    (h25 : m1 25 = (r : ℤ)) (h2 : m1 2 = 0) (h3 : m1 3 = 1) (h4 : m1 4 = 2) (h5 : m1 5 = 3)
    (h6 : m1 6 = 4) (h7 : m1 7 = 5) (h11 : m1 11 = 0) (h12 : m1 12 = 0) (h23 : m1 23 = 0)
    (hpre : ∀ p ∈ inp, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25) (hnd : inp.Nodup)
    (hdisj : ∀ p ∈ inp, ∀ p' ∈ inp, p.1 ≠ p'.2)
    (hdisj2 : ∀ p ∈ inp, ∀ p' ∈ inp, p ≠ p' → p.2 ≠ p'.2)
    (hval : ∀ p ∈ inp, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m1 p.1 = (q : ℤ))
    (hrun2 : Run (Nprog inp) (inp.length * (18 + (40*(r+1)*(r+1)+100))) ⟨0, m1⟩ = ⟨(Nprog inp).length, m'⟩)
    (hlT : ∀ p ∈ inp, ∀ q : ℕ, Odd q → 1 ≤ q → q < 2^r → m1 p.1 = (q : ℤ) →
      LogSpec r q (m' p.2)) :
    Run (first ++ shiftProg first.length (Nprog inp))
        (T1 + inp.length * (18 + (40*(r+1)*(r+1)+100))) ⟨0, m⟩
      = ⟨(first ++ shiftProg first.length (Nprog inp)).length, m'⟩ := by
  rw [Run_concat first (Nprog inp) T1 (inp.length * (18 + (40*(r+1)*(r+1)+100))) ⟨0, m⟩ hpc
    (by rw [hfirst])]
  rw [hfirst, hrun2, List.length_append, shiftProg_length]

end BkSet.RAM

end


-- ===============================================================================================
-- ============  Section `Theorem1main` merges two steps of the algorithm   ======================
-- ===============================================================================================

section

/-
# Theorem 1: the merged prime-generation + discrete-logarithm algorithm

This module formalises the merge step of Theorem 1.  Building on section
`Theorem1` (generic program concatenation `Run_concat`, the `N`-fold discrete
logarithm `lemma1_N`) it supplies

* the group theory that turns `LogSpec` (the output guarantee of the log routine) into the
  actual values `hz r hr i` of `H[n,k]` (`five_pow_inj`, `logspec_unique`, `logspec_neg`,
  `natCast_sub_two_pow`, `three_le_rOf`);
* `prog_agree` / `prog_run_agree` / `prog_run_frame`: the prime generator can be run from a
  memory that additionally carries `r` in register `25`, which is preserved;
* `Sprog` (`Sconst`, `Sdouble`, `Sinput`): the setup program between the two halves -- it
  fixes the constant registers of the log routine, computes `2^r` by doubling, and stores
  `2^r - p_j` in register `1000+(n+1)+j` (`Sprog_spec`);
* `inpList n`: the `2n` (input,output) register pairs handed to `Nprog`, and `Sel n`: the
  final selection program that combines the two logarithms of each prime (`Sel_spec`).

The register layout is collision-free for every `n`: the prime generator stores `p_j` in
`1000+j` (the offsets are forced by `PrimeGen`), while everything the setup and the
selector write lives above `1000+n`.

### Status

Both halves are ready to be joined and all of their specifications are proved (`prime_part`
for the prime generator carrying `r` in register `25`, `Sprog_spec`, `Nprog_spec` and
`Sel_spec`), but the final `theorem1` statement assembling them with `Run_concat` is *not*
yet written.  Two remaining technical points are worth recording:

* `PrimeGen.prog` ends in `Op.halt` at pc `19`, so the first part of the merged program must
  be `prog.take 19` (the trace is identical, but `Run_concat` needs the pc to *reach*
  `19 = (prog.take 19).length`, hence `main_bounded_all`'s halting time has to be replaced by
  the *first* time pc `19` is reached);
* the paper's amplitude bound `-1 .. 2^(2r) + O(1)` is proved for the setup and the
  logarithm blocks (`lemma1_amp`), but the bookkeeping that turns it into a bound on the
  *final* memory of the merged program (via `AInv` for the last logarithm block and the
  register frames) is still missing.
-/


namespace BkSet.RAM

open Nat

set_option maxHeartbeats 4000000

/-! ### Group-theoretic layer -/

theorem five_pow_inj (r : ℕ) (hr : 2 ≤ r) {a b : ℕ} (ha : a < 2^(r-2)) (hb : b < 2^(r-2))
    (h : (5 : ZMod (2^r))^a = (5 : ZMod (2^r))^b) : a = b := by
  have h' : (BkSet.fiveUnit r)^a = (BkSet.fiveUnit r)^b := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, BkSet.fiveUnit, ZMod.coe_unitOfCoprime]
    exact h
  have hmod := pow_eq_pow_iff_modEq.mp h'
  rw [BkSet.orderOf_five r hr] at hmod
  exact Nat.ModEq.eq_of_lt_of_lt hmod ha hb

theorem five_pow_ne_neg_one (r : ℕ) (hr : 2 ≤ r) (a : ℕ) :
    (5 : ZMod (2^r))^a ≠ -1 := by
  intro h
  have h' : (BkSet.fiveUnit r)^a = (-1 : (ZMod (2^r))ˣ) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, BkSet.fiveUnit, ZMod.coe_unitOfCoprime,
      Units.val_neg, Units.val_one]
    exact h
  have hmap := congrArg (ZMod.unitsMap (BkSet.four_dvd_two_pow r hr)) h'
  rw [map_pow, BkSet.unitsMap_five, BkSet.unitsMap_negOne, one_pow] at hmap
  have h2 : ((1 : (ZMod 4)ˣ) : ZMod 4) = (((-1 : (ZMod 4)ˣ)) : ZMod 4) :=
    congrArg (fun u : (ZMod 4)ˣ => (u : ZMod 4)) hmap
  simp only [Units.val_neg, Units.val_one] at h2
  exact absurd h2 (by decide)

theorem natCast_sub_two_pow (r p : ℕ) (hp : p ≤ 2^r) :
    (((2^r - p : ℕ)) : ZMod (2^r)) = -((p : ℕ) : ZMod (2^r)) := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, Nat.sub_add_cancel hp, ZMod.natCast_self]

theorem logspec_unique (r : ℕ) (hr : 2 ≤ r) (q h : ℕ) (o : ℤ)
    (hh : h < 2^(r-2)) (hq : ((q : ℤ) : ZMod (2^r)) = (5 : ZMod (2^r))^h)
    (hspec : LogSpec r q o) : o = (h : ℤ) := by
  rcases hspec with ⟨a, ha, hqa, ho⟩ | ⟨ho, hne⟩
  · have h2 : (5 : ZMod (2^r))^a = (5 : ZMod (2^r))^h := by rw [← hqa, hq]
    have := five_pow_inj r hr ha hh h2
    rw [ho, this]
  · exact absurd hq (hne h hh)

theorem logspec_neg (r : ℕ) (hr : 2 ≤ r) (q h : ℕ) (o : ℤ)
    (hh : h < 2^(r-2)) (hq : ((q : ℤ) : ZMod (2^r)) = -((5 : ZMod (2^r))^h))
    (hspec : LogSpec r q o) : o = -1 := by
  rcases hspec with ⟨a, ha, hqa, ho⟩ | ⟨ho, _⟩
  · exfalso
    have h2 : (5 : ZMod (2^r))^a = -((5 : ZMod (2^r))^h) := by rw [← hqa, hq]
    have hone : (5 : ZMod (2^r))^h * (5 : ZMod (2^r))^(2^(r-2) - h) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hh), five_pow_orderOf r hr]
    have hpow : (5 : ZMod (2^r))^(a + (2^(r-2) - h)) = -1 := by
      calc (5 : ZMod (2^r))^(a + (2^(r-2) - h))
          = (5 : ZMod (2^r))^a * (5 : ZMod (2^r))^(2^(r-2) - h) := by rw [pow_add]
        _ = (-(5 : ZMod (2^r))^h) * (5 : ZMod (2^r))^(2^(r-2) - h) := by rw [h2]
        _ = -((5 : ZMod (2^r))^h * (5 : ZMod (2^r))^(2^(r-2) - h)) := by rw [neg_mul]
        _ = -1 := by rw [hone]
    exact five_pow_ne_neg_one r hr _ hpow
  · exact ho

theorem three_le_rOf (n k : ℕ) (hk : 2 ≤ k) : 3 ≤ BkSet.rOf n k := by
  rw [BkSet.rOf]
  set P : ℕ := BkSet.oddPrime (n - 1) with hP
  have hP3 : 3 ≤ P := by rw [hP]; exact BkSet.three_le_oddPrime (n - 1)
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hlog : (1 : ℝ) < Real.logb 2 ((P : ℕ) : ℝ) := by
    have h2 : Real.logb 2 (2 : ℝ) = 1 := by simp
    rw [← h2, Real.logb_lt_logb_iff (b := 2) (by norm_num : (1:ℝ) < 2) (by norm_num : (0:ℝ) < 2) hPpos]
    exact_mod_cast (by omega : 2 < P)
  have hx : (2 : ℝ) < (k : ℝ) * Real.logb 2 ((P : ℕ) : ℝ) := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : (2 : ℝ) * 1 < (2 : ℝ) * Real.logb 2 ((P : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hlog (by norm_num)
    nlinarith
  have hceil : 2 < Nat.ceil ((k : ℝ) * Real.logb 2 ((P : ℕ) : ℝ)) := by
    rw [Nat.lt_ceil (α := ℝ)]; exact hx
  omega

/-! ### The prime generator as the first part of the merged algorithm -/

/-- Registers the prime generator `prog` can ever read or write. -/
def PGmem (n i : ℕ) : Prop := i < 16 ∨ (1000 ≤ i ∧ i < 1000 + n)

theorem update_agree {d : ℕ} {v v' : ℤ} {P : ℕ → Prop} {m m' : ℕ → ℤ}
    (h : ∀ i, P i → m i = m' i) (hvv : v = v') :
    ∀ i, P i → (Function.update m d v) i = (Function.update m' d v') i := by
  intro i hi
  by_cases hid : i = d
  · subst hid; rw [Function.update_self, Function.update_self, hvv]
  · rw [Function.update_of_ne hid, Function.update_of_ne hid]; exact h i hi

theorem prog_step_agree (n : ℕ) (pc : ℕ) (m m' : ℕ → ℤ)
    (h : ∀ i, PGmem n i → m i = m' i) :
    (step ⟨pc, m⟩).pc = (step ⟨pc, m'⟩).pc ∧
    ∀ i, PGmem n i → (step ⟨pc, m⟩).mem i = (step ⟨pc, m'⟩).mem i := by
  have h0 := h 0 (by simp [PGmem])
  have h1 := h 1 (by simp [PGmem])
  have h2 := h 2 (by simp [PGmem])
  have h3 := h 3 (by simp [PGmem])
  have h4 := h 4 (by simp [PGmem])
  have h10 := h 10 (by simp [PGmem])
  have h11 := h 11 (by simp [PGmem])
  have h12 := h 12 (by simp [PGmem])
  have h13 := h 13 (by simp [PGmem])
  have h14 := h 14 (by simp [PGmem])
  have h15 := h 15 (by simp [PGmem])
  rcases Nat.lt_or_ge pc 20 with hp | hp
  · interval_cases pc
    · rw [st0]
      exact ⟨rfl, update_agree h (by rw [h1])⟩
    · rw [st1]
      exact ⟨rfl, update_agree h (by rw [h3, h1])⟩
    · by_cases hh : m 10 = m 0
      · rw [st2eq m hh, st2eq m' (h10.symm.trans (hh.trans h0))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st2ne m hh, st2ne m' (by intro hc; exact hh (h10.trans hc |>.trans h0.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st3]
      exact ⟨rfl, update_agree h (by rw [h2, h1])⟩
    · rw [st4]
      exact ⟨rfl, update_agree h (by rw [h3, h1])⟩
    · by_cases hh : m 12 = m 11
      · rw [st5eq m hh, st5eq m' (h12.symm.trans (hh.trans h11))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st5ne m hh, st5ne m' (by intro hc; exact hh (h12.trans hc |>.trans h11.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st6]
      exact ⟨rfl, update_agree h (by rw [h11, h12])⟩
    · by_cases hh : m 14 = m 1
      · rw [st7eq m hh, st7eq m' (h14.symm.trans (hh.trans h1))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st7ne m hh, st7ne m' (by intro hc; exact hh (h14.trans hc |>.trans h1.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st8]
      exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st9]
      exact ⟨rfl, update_agree h (by rw [h1])⟩
    · rw [st10]
      exact ⟨rfl, update_agree h (by rw [h12, h2])⟩
    · rw [st11]
      exact ⟨rfl, fun i hi => h i hi⟩
    · by_cases hh : m 13 = m 2
      · rw [st12eq m hh, st12eq m' (h13.symm.trans (hh.trans h2))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st12ne m hh, st12ne m' (by intro hc; exact hh (h13.trans hc |>.trans h2.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st13]
      exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st14]
      exact ⟨rfl, update_agree h (by rw [h4, h10])⟩
    · rw [st15]
      refine ⟨rfl, ?_⟩
      intro i hi
      have hd : (m 15).toNat = (m' 15).toNat := by rw [h15]
      rw [hd]
      exact update_agree h (by rw [h11]) i hi
    · rw [st16]
      exact ⟨rfl, update_agree h (by rw [h10, h2])⟩
    · rw [st17]
      exact ⟨rfl, update_agree h (by rw [h11, h2])⟩
    · rw [st18]
      exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st19]
      exact ⟨rfl, fun i hi => h i hi⟩
  · have hnone : prog[pc]? = none := by rw [List.getElem?_eq_none_iff]; simp [prog]; omega
    have hs : step ⟨pc, m⟩ = ⟨pc, m⟩ := by simp only [step, hnone]
    have hs' : step ⟨pc, m'⟩ = ⟨pc, m'⟩ := by simp only [step, hnone]
    rw [hs, hs']
    exact ⟨rfl, fun i hi => h i hi⟩

-- (redundant namespace line removed)
open Nat

theorem prog_run_agree (n : ℕ) (m m' : ℕ → ℤ) (h : ∀ i, PGmem n i → m i = m' i) :
    ∀ t pc, (run t ⟨pc, m⟩).pc = (run t ⟨pc, m'⟩).pc ∧
      ∀ i, PGmem n i → (run t ⟨pc, m⟩).mem i = (run t ⟨pc, m'⟩).mem i := by
  intro t
  induction t with
  | zero => intro pc; exact ⟨rfl, fun i hi => h i hi⟩
  | succ t ih =>
    intro pc
    have hs := prog_step_agree n (run t ⟨pc, m⟩).pc (run t ⟨pc, m⟩).mem (run t ⟨pc, m'⟩).mem (ih pc).2
    rw [run_succ, run_succ, state_pc_eq (s := run t ⟨pc, m⟩) rfl,
      state_pc_eq (s := run t ⟨pc, m'⟩) rfl, ← (ih pc).1]
    exact hs

/-- Invariant pinning the "constant" registers of the prime generator and the
`store`-address lower bound. -/
def FrameInv (pc : ℕ) (mem : ℕ → ℤ) : Prop :=
  mem 1 = 0 ∧ mem 2 = 1 ∧ mem 4 = 1000 ∧ (0 : ℤ) ≤ mem 10 ∧
    (pc = 15 → (1000 : ℤ) ≤ mem 15)

theorem FrameInv_self {pc : ℕ} {mem : ℕ → ℤ} (h : FrameInv pc mem) (pc' : ℕ) (hpc' : pc' ≠ 15) :
    FrameInv pc' mem := by
  obtain ⟨a1, a2, a4, a10, _⟩ := h
  exact ⟨a1, a2, a4, a10, fun hh => absurd hh hpc'⟩

theorem FrameInv_upd {d : ℕ} {v : ℤ} {pc : ℕ} {mem : ℕ → ℤ} (pc' : ℕ) (h : FrameInv pc mem)
    (hd1 : (1:ℕ) ≠ d) (hd2 : (2:ℕ) ≠ d) (hd4 : (4:ℕ) ≠ d)
    (hv10 : (0 : ℤ) ≤ (Function.update mem d v) 10)
    (hv15 : pc' = 15 → (1000:ℤ) ≤ (Function.update mem d v) 15) :
    FrameInv pc' (Function.update mem d v) := by
  obtain ⟨a1, a2, a4, a10, a15⟩ := h
  exact ⟨by rw [Function.update_of_ne hd1]; exact a1,
         by rw [Function.update_of_ne hd2]; exact a2,
         by rw [Function.update_of_ne hd4]; exact a4, hv10, hv15⟩

theorem FrameInv_upd_small {d : ℕ} {v : ℤ} {pc : ℕ} {mem : ℕ → ℤ} (pc' : ℕ)
    (h : FrameInv pc mem) (hd1 : (1:ℕ) ≠ d) (hd2 : (2:ℕ) ≠ d) (hd4 : (4:ℕ) ≠ d)
    (hv10 : (0 : ℤ) ≤ (Function.update mem d v) 10) (hpc' : pc' ≠ 15) :
    FrameInv pc' (Function.update mem d v) :=
  FrameInv_upd pc' h hd1 hd2 hd4 hv10 (fun hh => absurd hh hpc')

theorem prog_frame_step (pc : ℕ) (mem : ℕ → ℤ) (h : FrameInv pc mem) :
    FrameInv (step ⟨pc, mem⟩).pc (step ⟨pc, mem⟩).mem ∧
      ∀ i, (i < 10 ∨ 16 ≤ i) → i < 1000 → (step ⟨pc, mem⟩).mem i = mem i := by
  obtain ⟨a1, a2, a4, a10, a15⟩ := h
  have H : FrameInv pc mem := ⟨a1, a2, a4, a10, a15⟩
  rcases Nat.lt_or_ge pc 20 with hp | hp
  · interval_cases pc
    · rw [congrArg State.pc (st0 mem), congrArg State.mem (st0 mem)]
      exact ⟨FrameInv_upd_small 1 H (by decide) (by decide) (by decide)
              (by rw [Function.update_self, a1]; norm_num) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 10) _ mem⟩
    · rw [congrArg State.pc (st1 mem), congrArg State.mem (st1 mem)]
      exact ⟨FrameInv_upd_small 2 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 11) _ mem⟩
    · by_cases hh : mem 10 = mem 0
      · rw [congrArg State.pc (st2eq mem hh), congrArg State.mem (st2eq mem hh)]
        exact ⟨FrameInv_self H 19 (by decide), fun i _ _ => rfl⟩
      · rw [congrArg State.pc (st2ne mem hh), congrArg State.mem (st2ne mem hh)]
        exact ⟨FrameInv_self H 3 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st3 mem), congrArg State.mem (st3 mem)]
      exact ⟨FrameInv_upd_small 4 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 13) _ mem⟩
    · rw [congrArg State.pc (st4 mem), congrArg State.mem (st4 mem)]
      exact ⟨FrameInv_upd_small 5 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 12) _ mem⟩
    · by_cases hh : mem 12 = mem 11
      · rw [congrArg State.pc (st5eq mem hh), congrArg State.mem (st5eq mem hh)]
        exact ⟨FrameInv_self H 12 (by decide), fun i _ _ => rfl⟩
      · rw [congrArg State.pc (st5ne mem hh), congrArg State.mem (st5ne mem hh)]
        exact ⟨FrameInv_self H 6 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st6 mem), congrArg State.mem (st6 mem)]
      exact ⟨FrameInv_upd_small 7 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 14)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 14) _ mem⟩
    · by_cases hh : mem 14 = mem 1
      · rw [congrArg State.pc (st7eq mem hh), congrArg State.mem (st7eq mem hh)]
        exact ⟨FrameInv_self H 9 (by decide), fun i _ _ => rfl⟩
      · rw [congrArg State.pc (st7ne mem hh), congrArg State.mem (st7ne mem hh)]
        exact ⟨FrameInv_self H 8 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st8 mem), congrArg State.mem (st8 mem)]
      exact ⟨FrameInv_self H 10 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st9 mem), congrArg State.mem (st9 mem)]
      exact ⟨FrameInv_upd_small 10 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 13)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 13) _ mem⟩
    · rw [congrArg State.pc (st10 mem), congrArg State.mem (st10 mem)]
      exact ⟨FrameInv_upd_small 11 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 12)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 12) _ mem⟩
    · rw [congrArg State.pc (st11 mem), congrArg State.mem (st11 mem)]
      exact ⟨FrameInv_self H 5 (by decide), fun i _ _ => rfl⟩
    · by_cases hh : mem 13 = mem 2
      · rw [congrArg State.pc (st12eq mem hh), congrArg State.mem (st12eq mem hh)]
        exact ⟨FrameInv_self H 14 (by decide), fun i _ _ => rfl⟩
      · rw [congrArg State.pc (st12ne mem hh), congrArg State.mem (st12ne mem hh)]
        exact ⟨FrameInv_self H 13 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st13 mem), congrArg State.mem (st13 mem)]
      exact ⟨FrameInv_self H 17 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st14 mem), congrArg State.mem (st14 mem)]
      refine ⟨FrameInv_upd 15 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 15)]; exact a10) ?_, ?_⟩
      · intro _; rw [Function.update_self, a4]; omega
      · intro i _ _
        exact Function.update_of_ne (by omega : i ≠ 15) _ mem
    · rw [congrArg State.pc (st15 mem), congrArg State.mem (st15 mem)]
      have h15 : (1000 : ℤ) ≤ mem 15 := a15 rfl
      refine ⟨FrameInv_upd 16 H (by omega) (by omega) (by omega)
              (by rw [Function.update_of_ne (by omega : (10:ℕ) ≠ (mem 15).toNat)]; exact a10)
              (by intro hh; omega), ?_⟩
      intro i _ _
      exact Function.update_of_ne (by omega : i ≠ (mem 15).toNat) _ mem
    · rw [congrArg State.pc (st16 mem), congrArg State.mem (st16 mem)]
      exact ⟨FrameInv_upd_small 17 H (by decide) (by decide) (by decide)
              (by rw [Function.update_self]; omega) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 10) _ mem⟩
    · rw [congrArg State.pc (st17 mem), congrArg State.mem (st17 mem)]
      exact ⟨FrameInv_upd_small 18 H (by decide) (by decide) (by decide)
              (by rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 11)]; exact a10) (by decide),
             fun i _ _ => Function.update_of_ne (by omega : i ≠ 11) _ mem⟩
    · rw [congrArg State.pc (st18 mem), congrArg State.mem (st18 mem)]
      exact ⟨FrameInv_self H 2 (by decide), fun i _ _ => rfl⟩
    · rw [congrArg State.pc (st19 mem), congrArg State.mem (st19 mem)]
      exact ⟨FrameInv_self H 19 (by decide), fun i _ _ => rfl⟩
  · have hnone : prog[pc]? = none := by rw [List.getElem?_eq_none_iff]; simp [prog]; omega
    have hs : step ⟨pc, mem⟩ = ⟨pc, mem⟩ := by simp only [step, hnone]
    rw [hs]
    exact ⟨FrameInv_self H pc (by omega), fun i _ _ => rfl⟩

theorem prog_run_frame (m : ℕ → ℤ) (pc : ℕ) (h : FrameInv pc m) :
    ∀ t, FrameInv (run t ⟨pc, m⟩).pc (run t ⟨pc, m⟩).mem ∧
      ∀ i, (i < 10 ∨ 16 ≤ i) → i < 1000 → (run t ⟨pc, m⟩).mem i = m i := by
  intro t
  induction t with
  | zero => exact ⟨h, fun i _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨hfinv, hframe⟩ := ih
    obtain ⟨h2finv, h2frame⟩ := prog_frame_step (run t ⟨pc, m⟩).pc (run t ⟨pc, m⟩).mem hfinv
    rw [run_succ]
    exact ⟨h2finv, fun i hi1 hi2 => by rw [h2frame i hi1 hi2]; exact hframe i hi1 hi2⟩

/-- Running the prime generator from a memory that additionally carries `r` in register `25`. -/
theorem prime_part (n r : ℕ) :
    ∃ T ≤ 700 * (n + 2)^4 + 100, ∃ mem : ℕ → ℤ,
      run T ⟨0, Function.update (initMem (n+1)) 25 (r : ℤ)⟩ = ⟨19, mem⟩ ∧
      mem 25 = (r : ℤ) ∧
      (∀ j, j < n+1 → mem (1000 + j) = (Nat.nth Nat.Prime j : ℤ)) ∧
      mem 0 = (n : ℤ) + 1 ∧ mem 1 = 0 ∧ mem 2 = 1 ∧ mem 3 = 2 ∧ mem 4 = 1000 ∧
      (∀ i, 16 ≤ i → i < 1000 → i ≠ 25 → mem i = 0) := by
  obtain ⟨T, hT, mem, hrun, hout, hamp⟩ := main_bounded_all (n+1)
  set m' : ℕ → ℤ := Function.update (initMem (n+1)) 25 (r : ℤ) with hm'
  have hagree0 : ∀ i, PGmem (n+1) i → (initMem (n+1)) i = m' i := by
    intro i hi
    have hi25 : i ≠ 25 := by rcases hi with h | ⟨h1, h2⟩ <;> omega
    rw [hm', Function.update_of_ne hi25]
  obtain ⟨hpc, hmem⟩ := prog_run_agree (n+1) (initMem (n+1)) m' hagree0 T 0
  have hpc19 : (run T ⟨0, m'⟩).pc = 19 := by
    rw [← hpc, show (run T ⟨0, initMem (n+1)⟩).pc = 19 from congrArg State.pc hrun]
  have hrun' : run T ⟨0, m'⟩ = ⟨19, (run T ⟨0, m'⟩).mem⟩ := state_pc_eq hpc19
  have h21 : m' 1 = 0 := by rw [hm', Function.update_of_ne (by decide : (1:ℕ) ≠ 25)]; simp [initMem]
  have h22 : m' 2 = 1 := by rw [hm', Function.update_of_ne (by decide : (2:ℕ) ≠ 25)]; simp [initMem]
  have h24 : m' 4 = 1000 := by rw [hm', Function.update_of_ne (by decide : (4:ℕ) ≠ 25)]; simp [initMem, BASE]
  have h210 : (0:ℤ) ≤ m' 10 := by rw [hm', Function.update_of_ne (by decide : (10:ℕ) ≠ 25)]; simp [initMem]
  have hfinv0 : FrameInv 0 m' := ⟨h21, h22, h24, h210, fun hh => absurd hh (by omega)⟩
  obtain ⟨hF, hframe⟩ := prog_run_frame m' 0 hfinv0 T
  have h25 : (run T ⟨0, m'⟩).mem 25 = (r : ℤ) := by
    rw [hframe 25 (by omega) (by omega), hm', Function.update_self]
  have hsm : (run T ⟨0, initMem (n+1)⟩).mem = mem := by
    rw [show (⟨0, initMem (n+1)⟩ : State) = s0 (n+1) from rfl]
    exact congrArg State.mem hrun
  have him : ∀ i, (i < 10 ∨ 16 ≤ i) → i < 1000 → i ≠ 25 → (run T ⟨0, m'⟩).mem i = (initMem (n+1)) i := by
    intro i hi hi2 hi3
    rw [hframe i hi hi2, hm', Function.update_of_ne hi3]
  refine ⟨T, hT, (run T ⟨0, m'⟩).mem, hrun', h25, fun j hj => by
    rw [← hmem (1000 + j) (Or.inr ⟨by omega, by omega⟩), hsm]
    simpa [BASE] using hout j hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [him 0 (by omega) (by omega) (by omega)]; simp [initMem]
  · rw [him 1 (by omega) (by omega) (by omega)]; simp [initMem]
  · rw [him 2 (by omega) (by omega) (by omega)]; simp [initMem]
  · rw [him 3 (by omega) (by omega) (by omega)]; simp [initMem]
  · rw [him 4 (by omega) (by omega) (by omega)]; simp [initMem, BASE]
  · intro i hi hi2 hi3
    rw [him i (by omega) (by omega) hi3]
    simp only [initMem]
    rw [if_neg (by omega : ¬ (i = 0)), if_neg (by omega : ¬ (i = 2)), if_neg (by omega : ¬ (i = 3)),
      if_neg (by omega : ¬ (i = 4)), if_neg (by omega : ¬ (i = 11))]


-- (redundant namespace line removed)
open Nat

/-! ### The setup program `Sprog`

`Sprog` turns the prime generator's halting memory into the initial memory of the
`Nprog` logarithm blocks: it fixes the constant registers, copies `r` to `25` (already
there), computes `2^r` by doubling, and writes `2^r - p_j` into register `2000 + j`. -/

/-- Fixing the constant registers expected by the logarithm blocks. -/
def Sconst : List Op :=
  [Op.add 31 4 1, Op.add 4 2 2, Op.add 3 2 1, Op.sub 2 1 1, Op.add 5 4 3,
   Op.add 6 4 4, Op.add 7 5 4, Op.sub 11 1 1, Op.sub 12 1 1, Op.sub 23 1 1,
   Op.sub 35 0 3, Op.add 26 3 1, Op.sub 27 1 1]

def mc (m : ℕ → ℤ) : ℕ → ℤ :=
  let a0 := Function.update m 31 (m 4 + m 1)
  let a1 := Function.update a0 4 (a0 2 + a0 2)
  let a2 := Function.update a1 3 (a1 2 + a1 1)
  let a3 := Function.update a2 2 (a2 1 - a2 1)
  let a4 := Function.update a3 5 (a3 4 + a3 3)
  let a5 := Function.update a4 6 (a4 4 + a4 4)
  let a6 := Function.update a5 7 (a5 5 + a5 4)
  let a7 := Function.update a6 11 (a6 1 - a6 1)
  let a8 := Function.update a7 12 (a7 1 - a7 1)
  let a9 := Function.update a8 23 (a8 1 - a8 1)
  let a10 := Function.update a9 35 (a9 0 - a9 3)
  let a11 := Function.update a10 26 (a10 3 + a10 1)
  Function.update a11 27 (a11 1 - a11 1)

theorem Sconst_run (m : ℕ → ℤ) : Run Sconst 13 ⟨0, m⟩ = ⟨13, mc m⟩ := rfl

theorem Sconst_pc (m : ℕ → ℤ) : ∀ t ≤ 13, (Run Sconst t ⟨0, m⟩).pc = t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have hst : Run Sconst t ⟨0, m⟩ = ⟨t, (Run Sconst t ⟨0, m⟩).mem⟩ := state_pc_eq (ih (by omega))
    have ht13 : t < 13 := by omega
    rw [Run_succ, hst]
    interval_cases t <;> simp [stepP, Sconst, Op.exec]

theorem Sconst_consts (n r : ℕ) (m : ℕ → ℤ) (h1 : m 1 = 0) (h2 : m 2 = 1)
    (h0 : m 0 = (n : ℤ) + 1) (h3 : m 3 = 2) (h4 : m 4 = 1000) :
    (mc m) 2 = 0 ∧ (mc m) 3 = 1 ∧ (mc m) 4 = 2 ∧ (mc m) 5 = 3 ∧ (mc m) 6 = 4 ∧
      (mc m) 7 = 5 ∧ (mc m) 11 = 0 ∧ (mc m) 12 = 0 ∧ (mc m) 23 = 0 ∧ (mc m) 31 = 1000 ∧
      (mc m) 26 = 1 ∧ (mc m) 27 = 0 ∧ (mc m) 35 = (n : ℤ) ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 11 → i ≠ 12 → i ≠ 23 →
        i ≠ 26 → i ≠ 27 → i ≠ 31 → i ≠ 35 → (mc m) i = m i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mc, h1]
  · simp [mc, h1, h2]
  · simp [mc, h2]
  · simp [mc, h1, h2]
  · simp [mc, h2]
  · simp [mc, h1, h2]
  · simp [mc, h1]
  · simp [mc, h1]
  · simp [mc, h1]
  · simp [mc, h1, h4]
  · simp [mc, h1, h2]
  · simp [mc, h1]
  · simp [mc, h0, h1, h2, h3]
  · intro i hi2 hi3 hi4 hi5 hi6 hi7 hi11 hi12 hi23 hi26 hi27 hi31 hi35
    simp only [mc]
    rw [Function.update_of_ne hi27, Function.update_of_ne hi26, Function.update_of_ne hi35,
      Function.update_of_ne hi23, Function.update_of_ne hi12, Function.update_of_ne hi11,
      Function.update_of_ne hi7, Function.update_of_ne hi6, Function.update_of_ne hi5,
      Function.update_of_ne hi2, Function.update_of_ne hi3, Function.update_of_ne hi4,
      Function.update_of_ne hi31]


-- (redundant namespace line removed)
open Nat

theorem Run_one (P : List Op) (s : State) : Run P 1 s = stepP P s := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Run_succ, Run_zero]

/-! #### The doubling loop -/

def Sdouble : List Op := [Op.jeq 27 25 4, Op.add 26 26 26, Op.add 27 27 3, Op.jmp 0]

def Sd1m (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 26 (mm 26 + mm 26)
def Sd2m (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 27 (mm 27 + mm 3)
def Sdbody (mm : ℕ → ℤ) : ℕ → ℤ := Sd2m (Sd1m mm)

theorem Sd0 (mm : ℕ → ℤ) (h : mm 27 = mm 25) : stepP Sdouble ⟨0, mm⟩ = ⟨4, mm⟩ := by
  simp [stepP, Sdouble, Op.exec, h]
theorem Sd0' (mm : ℕ → ℤ) (h : mm 27 ≠ mm 25) : stepP Sdouble ⟨0, mm⟩ = ⟨1, mm⟩ := by
  simp [stepP, Sdouble, Op.exec, h]
theorem Sd1 (mm : ℕ → ℤ) : stepP Sdouble ⟨1, mm⟩ = ⟨2, Sd1m mm⟩ := by
  simp [stepP, Sdouble, Op.exec, Sd1m]
theorem Sd2 (mm : ℕ → ℤ) : stepP Sdouble ⟨2, mm⟩ = ⟨3, Sd2m mm⟩ := by
  simp [stepP, Sdouble, Op.exec, Sd2m]
theorem Sd3 (mm : ℕ → ℤ) : stepP Sdouble ⟨3, mm⟩ = ⟨0, mm⟩ := by
  simp [stepP, Sdouble, Op.exec]
theorem Sdl (mm : ℕ → ℤ) : stepP Sdouble ⟨4, mm⟩ = ⟨4, mm⟩ := by
  simp [stepP, Sdouble]

theorem Sdbody_run (mm : ℕ → ℤ) (h : mm 27 ≠ mm 25) :
    Run Sdouble 4 ⟨0, mm⟩ = ⟨0, Sdbody mm⟩ := by
  simp only [Run_succ, Run_zero, Sd0' mm h, Sd1, Sd2, Sd3, Sdbody]

theorem Sdbody_26 (mm : ℕ → ℤ) : Sdbody mm 26 = mm 26 + mm 26 := by
  simp [Sdbody, Sd2m, Sd1m]
theorem Sdbody_27 (mm : ℕ → ℤ) : Sdbody mm 27 = mm 27 + mm 3 := by
  simp [Sdbody, Sd2m, Sd1m]
theorem Sdbody_25 (mm : ℕ → ℤ) : Sdbody mm 25 = mm 25 := by
  simp [Sdbody, Sd2m, Sd1m]
theorem Sdbody_3 (mm : ℕ → ℤ) : Sdbody mm 3 = mm 3 := by
  simp [Sdbody, Sd2m, Sd1m]
theorem Sdbody_frame (mm : ℕ → ℤ) {i : ℕ} (h1 : i ≠ 26) (h2 : i ≠ 27) :
    Sdbody mm i = mm i := by
  simp [Sdbody, Sd2m, Sd1m, Function.update_of_ne h1, Function.update_of_ne h2]

theorem Sdouble_run (k : ℕ) : ∀ (mem : ℕ → ℤ) (C : ℕ),
    mem 25 = (C : ℤ) → mem 27 = (C : ℤ) - (k : ℤ) → mem 3 = 1 →
    ∃ mfin : ℕ → ℤ, Run Sdouble (4 * k + 1) ⟨0, mem⟩ = ⟨4, mfin⟩ ∧
      mfin 26 = mem 26 * (2 : ℤ) ^ k ∧ mfin 27 = (C : ℤ) ∧
      (∀ i, i ≠ 26 → i ≠ 27 → mfin i = mem i) := by
  induction k with
  | zero =>
    intro mem C h25 h27 h3
    have heq : mem 27 = mem 25 := by rw [h25, h27]; simp
    refine ⟨mem, ?_, ?_, ?_, ?_⟩
    · rw [show 4 * 0 + 1 = 1 from rfl, Run_one]; exact Sd0 mem heq
    · simp
    · rw [h27]; ring
    · intro i _ _; rfl
  | succ k ih =>
    intro mem C h25 h27 h3
    have hne : mem 27 ≠ mem 25 := by rw [h25, h27]; intro hc; omega
    obtain ⟨mfin, hrun, h26, h27', hfr⟩ :=
      ih (Sdbody mem) C (Sdbody_25 mem ▸ h25)
        (by rw [Sdbody_27 mem, h27, h3]; push_cast; ring)
        (by rw [Sdbody_3 mem, h3])
    refine ⟨mfin, ?_, ?_, ?_, ?_⟩
    · rw [show 4 * (k + 1) + 1 = 4 + (4 * k + 1) from by ring, Run_add, Sdbody_run mem hne, hrun]
    · rw [h26, Sdbody_26 mem, show (2:ℤ) ^ (k+1) = 2 ^ k * 2 from by rw [pow_succ]]
      ring
    · exact h27'
    · intro i h1 h2
      rw [hfr i h1 h2, Sdbody_frame mem h1 h2]


-- (redundant namespace line removed)
open Nat

/-! #### The `pc` trace of the doubling loop (needed to splice it) -/

theorem Sdouble_head (mem : ℕ → ℤ) (r : ℕ) (h27 : mem 27 = 0) (h25 : mem 25 = (r:ℤ))
    (h3 : mem 3 = 1) :
    ∀ k ≤ r, (Run Sdouble (4*k) ⟨0, mem⟩).pc = 0 ∧ (Run Sdouble (4*k) ⟨0, mem⟩).mem 27 = (k:ℤ) ∧
      (Run Sdouble (4*k) ⟨0, mem⟩).mem 26 = mem 26 * (2:ℤ)^k ∧
      (Run Sdouble (4*k) ⟨0, mem⟩).mem 25 = mem 25 ∧ (Run Sdouble (4*k) ⟨0, mem⟩).mem 3 = mem 3 := by
  intro k
  induction k with
  | zero => intro _; refine ⟨rfl, h27, by simp, rfl, rfl⟩
  | succ k ih =>
    intro hk
    set M : ℕ → ℤ := (Run Sdouble (4*k) ⟨0, mem⟩).mem with hM
    obtain ⟨hp, hm27, hm26, hm25, hm3⟩ := ih (by omega)
    have hkmem : Run Sdouble (4*k) ⟨0, mem⟩ = ⟨0, M⟩ := state_pc_eq hp
    have hne : M 27 ≠ M 25 := by rw [hm27, hm25, h25]; omega
    have hbody : Run Sdouble (4*(k+1)) ⟨0, mem⟩ = ⟨0, Sdbody M⟩ := by
      rw [show 4*(k+1) = 4*k + 4 from by ring, Run_add, hkmem, Sdbody_run _ hne]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbody]
    · rw [hbody]; show Sdbody M 27 = ((k+1 : ℕ) : ℤ)
      rw [Sdbody_27, hm27, hm3, h3]; push_cast; ring
    · rw [hbody]; show Sdbody M 26 = mem 26 * (2:ℤ)^(k+1)
      rw [Sdbody_26, hm26, show (2:ℤ)^(k+1) = (2:ℤ)^k * 2 from by rw [pow_succ]]; ring
    · rw [hbody]; show Sdbody M 25 = mem 25
      rw [Sdbody_25, hm25]
    · rw [hbody]; show Sdbody M 3 = mem 3
      rw [Sdbody_3, hm3]

theorem Sdouble_pc_lt (mem : ℕ → ℤ) (r : ℕ) (h27 : mem 27 = 0) (h25 : mem 25 = (r:ℤ))
    (h3 : mem 3 = 1) : ∀ t < 4*r + 1, (Run Sdouble t ⟨0, mem⟩).pc < 4 := by
  intro t ht
  set k : ℕ := t / 4 with hk
  set j : ℕ := t % 4 with hj
  have htjk : 4*k + j = t := by rw [hk, hj]; exact Nat.div_add_mod t 4
  have hj4 : j < 4 := by rw [hj]; exact Nat.mod_lt _ (by norm_num)
  have hkr : k ≤ r := by rw [hk]; omega
  obtain ⟨hp, hm27, _, hm25, hm3⟩ := Sdouble_head mem r h27 h25 h3 k hkr
  set M : ℕ → ℤ := (Run Sdouble (4*k) ⟨0, mem⟩).mem with hM
  have hkmem : Run Sdouble (4*k) ⟨0, mem⟩ = ⟨0, M⟩ := state_pc_eq hp
  rcases Nat.lt_or_ge k r with hlt | hge
  · have hne : M 27 ≠ M 25 := by rw [hm27, hm25, h25]; omega
    have hs1 : Run Sdouble (4*k+1) ⟨0, mem⟩ = ⟨1, M⟩ := by
      rw [show 4*k+1 = 4*k + 1 from by ring, Run_add, hkmem, Run_one]; exact Sd0' M hne
    have hs2 : Run Sdouble (4*k+2) ⟨0, mem⟩ = ⟨2, Sd1m M⟩ := by
      rw [show 4*k+2 = (4*k+1) + 1 from by ring, Run_add, hs1, Run_one]; exact Sd1 M
    have hs3 : Run Sdouble (4*k+3) ⟨0, mem⟩ = ⟨3, Sd2m (Sd1m M)⟩ := by
      rw [show 4*k+3 = (4*k+2) + 1 from by ring, Run_add, hs2, Run_one]; exact Sd2 (Sd1m M)
    rw [← htjk]
    interval_cases j
    · rw [show 4*k+0 = 4*k from by ring, hkmem]; show (0:ℕ) < 4; norm_num
    · rw [hs1]; show (1:ℕ) < 4; norm_num
    · rw [hs2]; show (2:ℕ) < 4; norm_num
    · rw [hs3]; show (3:ℕ) < 4; norm_num
  · have hkeq : k = r := by omega
    have hj0 : j = 0 := by rw [← htjk, hkeq] at ht; omega
    have ht4k : t = 4*k := by rw [← htjk, hj0]; ring
    rw [ht4k, hkmem]
    show (0:ℕ) < 4
    norm_num

/-! #### The negation loop -/

def Sinput : List Op :=
  [Op.add 30 31 0, Op.add 28 3 1, Op.jgt 28 35 10, Op.add 29 31 28, Op.load 32 29,
   Op.add 33 30 28, Op.sub 34 26 32, Op.store 33 34, Op.add 28 28 3, Op.jmp 2]

def Si30 (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 30 (mm 31 + mm 0)
def Si28 (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 28 (mm 3 + mm 1)
def SiA (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 29 (mm 31 + mm 28)
def SiB (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 32 (mm (mm 29).toNat)
def SiC (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 33 (mm 30 + mm 28)
def SiD (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 34 (mm 26 - mm 32)
def SiE (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm (mm 33).toNat (mm 34)
def SiF (mm : ℕ → ℤ) : ℕ → ℤ := Function.update mm 28 (mm 28 + mm 3)
def Sbody (mm : ℕ → ℤ) : ℕ → ℤ := SiF (SiE (SiD (SiC (SiB (SiA mm)))))

theorem Si0 (mm : ℕ → ℤ) : stepP Sinput ⟨0, mm⟩ = ⟨1, Si30 mm⟩ := by simp [stepP, Sinput, Op.exec, Si30]
theorem Si1 (mm : ℕ → ℤ) : stepP Sinput ⟨1, mm⟩ = ⟨2, Si28 mm⟩ := by simp [stepP, Sinput, Op.exec, Si28]
theorem Si2g (mm : ℕ → ℤ) (h : mm 28 > mm 35) : stepP Sinput ⟨2, mm⟩ = ⟨10, mm⟩ := by
  simp [stepP, Sinput, Op.exec, h]
theorem Si2l (mm : ℕ → ℤ) (h : ¬ mm 28 > mm 35) : stepP Sinput ⟨2, mm⟩ = ⟨3, mm⟩ := by
  simp [stepP, Sinput, Op.exec, h]
theorem Si3 (mm : ℕ → ℤ) : stepP Sinput ⟨3, mm⟩ = ⟨4, SiA mm⟩ := by simp [stepP, Sinput, Op.exec, SiA]
theorem Si4 (mm : ℕ → ℤ) : stepP Sinput ⟨4, mm⟩ = ⟨5, SiB mm⟩ := by simp [stepP, Sinput, Op.exec, SiB]
theorem Si5 (mm : ℕ → ℤ) : stepP Sinput ⟨5, mm⟩ = ⟨6, SiC mm⟩ := by simp [stepP, Sinput, Op.exec, SiC]
theorem Si6 (mm : ℕ → ℤ) : stepP Sinput ⟨6, mm⟩ = ⟨7, SiD mm⟩ := by simp [stepP, Sinput, Op.exec, SiD]
theorem Si7 (mm : ℕ → ℤ) : stepP Sinput ⟨7, mm⟩ = ⟨8, SiE mm⟩ := by simp [stepP, Sinput, Op.exec, SiE]
theorem Si8 (mm : ℕ → ℤ) : stepP Sinput ⟨8, mm⟩ = ⟨9, SiF mm⟩ := by simp [stepP, Sinput, Op.exec, SiF]
theorem Si9 (mm : ℕ → ℤ) : stepP Sinput ⟨9, mm⟩ = ⟨2, mm⟩ := by simp [stepP, Sinput, Op.exec]
theorem Sil (mm : ℕ → ℤ) : stepP Sinput ⟨10, mm⟩ = ⟨10, mm⟩ := by simp [stepP, Sinput]

theorem Sbody_run (mm : ℕ → ℤ) (h : ¬ mm 28 > mm 35) :
    Run Sinput 8 ⟨2, mm⟩ = ⟨2, Sbody mm⟩ := by
  simp only [Run_succ, Run_zero, Si2l mm h, Si3, Si4, Si5, Si6, Si7, Si8, Si9, Sbody]

/-- State invariant of the negation loop.  The negated primes are written to the registers
`1000 + (N+1) + j`, which lie above the prime cells `1000 + j`. -/
structure InInv (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) : Prop where
  s0  : mem 0 = (N : ℤ) + 1
  s1  : mem 1 = 0
  s3  : mem 3 = 1
  s26 : mem 26 = (2 : ℤ) ^ r
  s28 : mem 28 = (k : ℤ) + 1
  s30 : mem 30 = 1000 + ((N : ℤ) + 1)
  s31 : mem 31 = 1000
  s35 : mem 35 = (N : ℤ)
  inp : ∀ j, 1 ≤ j → j ≤ N → mem (1000 + j) = (pj j : ℤ)
  out : ∀ j, 1 ≤ j → j ≤ k → mem (1000 + (N + 1) + j) = (2 : ℤ) ^ r - (pj j : ℤ)

theorem Sbody_a5 (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) {i : ℕ} (h29 : i ≠ 29) (h32 : i ≠ 32) (h33 : i ≠ 33)
    (h34 : i ≠ 34) (h2k : i ≠ 1000 + (N + 1) + (k + 1)) :
    SiE (SiD (SiC (SiB (SiA mem)))) i = mem i := by
  have h31 : mem 31 = 1000 := h.s31
  have h28' : mem 28 = (k : ℤ) + 1 := h.s28
  have h30 : mem 30 = 1000 + ((N : ℤ) + 1) := h.s30
  have e29 : SiA mem 29 = (1000 : ℤ) + ((k : ℤ) + 1) := by simp [SiA, h31, h28']
  have e29n : (SiA mem 29).toNat = 1000 + (k + 1) := by rw [e29]; omega
  have hA33 : SiA mem 33 = mem 33 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (33:ℕ) ≠ 29)]
  have hA30 : SiA mem 30 = mem 30 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (30:ℕ) ≠ 29)]
  have hA28 : SiA mem 28 = mem 28 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (28:ℕ) ≠ 29)]
  have hB30 : SiB (SiA mem) 30 = SiA mem 30 := by simp only [SiB]; rw [Function.update_of_ne (by omega : (30:ℕ) ≠ 32)]
  have hB28 : SiB (SiA mem) 28 = SiA mem 28 := by simp only [SiB]; rw [Function.update_of_ne (by omega : (28:ℕ) ≠ 32)]
  have hC33 : SiC (SiB (SiA mem)) 33 = SiB (SiA mem) 30 + SiB (SiA mem) 28 := by
    simp only [SiC, Function.update_self]
  have hD33 : SiD (SiC (SiB (SiA mem))) 33 = SiC (SiB (SiA mem)) 33 := by
    simp only [SiD]; rw [Function.update_of_ne (by omega : (33:ℕ) ≠ 34)]
  have hD33v : (SiD (SiC (SiB (SiA mem))) 33).toNat = 1000 + (N + 1) + (k + 1) := by
    rw [hD33, hC33, hB30, hB28, hA30, hA28, h30, h28']; omega
  have hA : SiA mem i = mem i := by simp only [SiA]; rw [Function.update_of_ne h29]
  have hB : SiB (SiA mem) i = SiA mem i := by
    simp only [SiB]; rw [Function.update_of_ne (by omega : i ≠ 32)]
  have hC : SiC (SiB (SiA mem)) i = SiB (SiA mem) i := by
    simp only [SiC]; rw [Function.update_of_ne h33]
  have hD : SiD (SiC (SiB (SiA mem))) i = SiC (SiB (SiA mem)) i := by
    simp only [SiD]; rw [Function.update_of_ne h34]
  have hE : SiE (SiD (SiC (SiB (SiA mem)))) i = SiD (SiC (SiB (SiA mem))) i := by
    simp only [SiE]
    rw [Function.update_of_ne (by omega : i ≠ ((SiD (SiC (SiB (SiA mem)))) 33).toNat)]
  rw [hE, hD, hC, hB, hA]

theorem Sbody_val (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) {i : ℕ} (h28 : i ≠ 28) (h29 : i ≠ 29) (h32 : i ≠ 32)
    (h33 : i ≠ 33) (h34 : i ≠ 34) (h2k : i ≠ 1000 + (N + 1) + (k + 1)) :
    Sbody mem i = mem i := by
  have h5 := Sbody_a5 r N pj k mem hk h h29 h32 h33 h34 h2k
  simp only [Sbody, SiF]
  rw [Function.update_of_ne h28, h5]

theorem Sbody_28 (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) : Sbody mem 28 = (k : ℤ) + 2 := by
  have h3 : mem 3 = 1 := h.s3
  have h28' : mem 28 = (k : ℤ) + 1 := h.s28
  have e1 := Sbody_a5 r N pj k mem hk h (i := 28) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e2 := Sbody_a5 r N pj k mem hk h (i := 3) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [Sbody, SiF]
  rw [Function.update_self, e1, e2, h28', h3]
  ring

theorem Sbody_2k (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) :
    Sbody mem (1000 + (N + 1) + (k + 1)) = (2 : ℤ) ^ r - (pj (k + 1) : ℤ) := by
  have h26 : mem 26 = (2 : ℤ) ^ r := h.s26
  have h31 : mem 31 = 1000 := h.s31
  have h28' : mem 28 = (k : ℤ) + 1 := h.s28
  have h30 : mem 30 = 1000 + ((N : ℤ) + 1) := h.s30
  have hpj : mem (1000 + (k + 1)) = (pj (k + 1) : ℤ) := h.inp (k + 1) (by omega) (by omega)
  have e29 : SiA mem 29 = (1000 : ℤ) + ((k : ℤ) + 1) := by simp [SiA, h31, h28']
  have e29n : (SiA mem 29).toNat = 1000 + (k + 1) := by rw [e29]; omega
  have hA26 : SiA mem 26 = mem 26 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (26:ℕ) ≠ 29)]
  have hA28 : SiA mem 28 = mem 28 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (28:ℕ) ≠ 29)]
  have hA30 : SiA mem 30 = mem 30 := by simp only [SiA]; rw [Function.update_of_ne (by omega : (30:ℕ) ≠ 29)]
  have hB30 : SiB (SiA mem) 30 = SiA mem 30 := by simp only [SiB]; rw [Function.update_of_ne (by omega : (30:ℕ) ≠ 32)]
  have hB28 : SiB (SiA mem) 28 = SiA mem 28 := by simp only [SiB]; rw [Function.update_of_ne (by omega : (28:ℕ) ≠ 32)]
  have hC33 : SiC (SiB (SiA mem)) 33 = SiB (SiA mem) 30 + SiB (SiA mem) 28 := by
    simp only [SiC, Function.update_self]
  have hD33 : SiD (SiC (SiB (SiA mem))) 33 = SiC (SiB (SiA mem)) 33 := by
    simp only [SiD]; rw [Function.update_of_ne (by omega : (33:ℕ) ≠ 34)]
  have hD33v : (SiD (SiC (SiB (SiA mem))) 33).toNat = 1000 + (N + 1) + (k + 1) := by
    rw [hD33, hC33, hB30, hB28, hA30, hA28, h30, h28']; omega
  have hB32 : SiB (SiA mem) 32 = (pj (k + 1) : ℤ) := by
    simp only [SiB]
    rw [Function.update_self, e29n]
    simp only [SiA]
    rw [Function.update_of_ne (by omega : (1000 + (k + 1)) ≠ 29)]
    exact hpj
  have hC26 : SiC (SiB (SiA mem)) 26 = mem 26 := by
    simp only [SiC]; rw [Function.update_of_ne (by omega : (26:ℕ) ≠ 33)]
    simp only [SiB]; rw [Function.update_of_ne (by omega : (26:ℕ) ≠ 32)]
    exact hA26
  have hC32 : SiC (SiB (SiA mem)) 32 = (pj (k + 1) : ℤ) := by
    simp only [SiC]; rw [Function.update_of_ne (by omega : (32:ℕ) ≠ 33)]
    exact hB32
  have hD34 : SiD (SiC (SiB (SiA mem))) 34
      = SiC (SiB (SiA mem)) 26 - SiC (SiB (SiA mem)) 32 := by
    simp only [SiD, Function.update_self]
  simp only [Sbody, SiF]
  rw [Function.update_of_ne (by omega : (1000 + (N+1) + (k+1) : ℕ) ≠ 28)]
  simp only [SiE]
  rw [hD33v, Function.update_self, hD34, hC26, hC32, h26]

theorem Sinput_loop (r N : ℕ) (pj : ℕ → ℕ) :
    ∀ (m : ℕ) (k : ℕ) (mem : ℕ → ℤ), k ≤ N → N - k ≤ m → InInv r N pj k mem →
    ∃ mfin, Run Sinput (8 * (N - k) + 1) ⟨2, mem⟩ = ⟨10, mfin⟩ ∧
      (∀ j, 1 ≤ j → j ≤ N → mfin (1000 + (N + 1) + j) = (2:ℤ)^r - (pj j : ℤ)) ∧
      (∀ j, 1 ≤ j → j ≤ N → mfin (1000 + j) = (pj j : ℤ)) ∧
      mfin 28 = (N : ℤ) + 1 ∧
      (∀ i, i ≠ 28 → i ≠ 29 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
        (∀ j, 1 ≤ j → j ≤ N → i ≠ 1000 + (N + 1) + j) → mfin i = mem i) := by
  intro m
  induction m with
  | zero =>
    intro k mem hk hm h
    have hkN : k = N := by omega
    have hgt : mem 28 > mem 35 := by rw [h.s28, h.s35, hkN]; omega
    refine ⟨mem, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 8 * (N - k) + 1 = 1 from by omega, Run_one]; exact Si2g mem hgt
    · exact fun j hj1 hjN => h.out j hj1 (by omega)
    · exact h.inp
    · rw [h.s28, hkN]
    · intro i _ _ _ _ _ _; rfl
  | succ m ih =>
    intro k mem hk hm h
    rcases Nat.lt_or_ge k N with hlt | hge
    · have hkn : k < N := hlt
      have hgt : ¬ (mem 28 > mem 35) := by rw [h.s28, h.s35]; omega
      have eBig : ∀ (X : ℕ), X ≤ 1000 + N → X ≠ 1000 + (N+1) + (k+1) := fun X hX => by omega
      have eBig2 : ∀ (X : ℕ), X ≤ 1000 + (N+1) + k → X ≠ 1000 + (N+1) + (k+1) := fun X hX => by omega
      have ev : ∀ i, i ≠ 28 → i ≠ 29 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
          i ≠ 1000 + (N+1) + (k+1) → Sbody mem i = mem i :=
        fun i a b c d e f => Sbody_val r N pj k mem hkn h a b c d e f
      have h26 : Sbody mem 26 = (2:ℤ)^r := by
        rw [ev 26 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 26 (by omega)), h.s26]
      have h30 : Sbody mem 30 = 1000 + ((N:ℤ)+1) := by
        rw [ev 30 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 30 (by omega)), h.s30]
      have hinp : ∀ j, 1 ≤ j → j ≤ N → Sbody mem (1000 + j) = (pj j : ℤ) := by
        intro j hj1 hjN
        rw [ev (1000+j) (by omega) (by omega) (by omega) (by omega) (by omega) (eBig (1000+j) (by omega)),
          h.inp j hj1 hjN]
      have hout : ∀ j, 1 ≤ j → j ≤ k + 1 → Sbody mem (1000 + (N+1) + j) = (2:ℤ)^r - (pj j : ℤ) := by
        intro j hj1 hjk
        rcases Nat.lt_or_ge j (k+1) with hjlt | hjge
        · rw [ev (1000+(N+1)+j) (by omega) (by omega) (by omega) (by omega) (by omega)
              (eBig2 (1000+(N+1)+j) (by omega)), h.out j hj1 (by omega)]
        · have hje : j = k + 1 := by omega
          subst hje
          rw [Sbody_2k r N pj k mem hkn h]
      have hinv : InInv r N pj (k+1) (Sbody mem) :=
        ⟨by rw [ev 0 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 0 (by omega)), h.s0],
         by rw [ev 1 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 1 (by omega)), h.s1],
         by rw [ev 3 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 3 (by omega)), h.s3],
         h26,
         by rw [Sbody_28 r N pj k mem hkn h]; push_cast; ring,
         h30,
         by rw [ev 31 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 31 (by omega)), h.s31],
         by rw [ev 35 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 35 (by omega)), h.s35],
         hinp, hout⟩
      obtain ⟨mfin, hrun, houtL, hinpL, h28L, hfrL⟩ :=
        ih (k+1) (Sbody mem) (by omega) (by omega) hinv
      refine ⟨mfin, ?_, houtL, hinpL, h28L, ?_⟩
      · rw [show 8 * (N - k) + 1 = 8 + (8 * (N - (k+1)) + 1) from by omega, Run_add,
            Sbody_run mem hgt, hrun]
      · intro i hi1 hi2 hi3 hi4 hi5 hi6
        rw [hfrL i hi1 hi2 hi3 hi4 hi5 hi6, ev i hi1 hi2 hi3 hi4 (by omega) (hi6 (k+1) (by omega) (by omega))]
    · have hkeq : k = N := by omega
      have hgt : mem 28 > mem 35 := by rw [h.s28, h.s35, hkeq]; omega
      refine ⟨mem, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 8 * (N - k) + 1 = 1 from by omega, Run_one]; exact Si2g mem hgt
      · exact fun j hj1 hjN => h.out j hj1 (by omega)
      · exact h.inp
      · rw [h.s28, hkeq]
      · intro i _ _ _ _ _ _; rfl

theorem Sinput_run (r N : ℕ) (pj : ℕ → ℕ) (mem : ℕ → ℤ)
    (h0 : mem 0 = (N:ℤ) + 1) (h1 : mem 1 = 0) (h3 : mem 3 = 1) (h31 : mem 31 = 1000)
    (h35 : mem 35 = (N:ℤ)) (h26 : mem 26 = (2:ℤ)^r)
    (hinp : ∀ j, 1 ≤ j → j ≤ N → mem (1000+j) = (pj j : ℤ)) :
    ∃ mfin, Run Sinput (8*N + 3) ⟨0, mem⟩ = ⟨10, mfin⟩ ∧
      (∀ j, 1 ≤ j → j ≤ N → mfin (1000+(N+1)+j) = (2:ℤ)^r - (pj j : ℤ)) ∧
      (∀ j, 1 ≤ j → j ≤ N → mfin (1000+j) = (pj j : ℤ)) ∧
      (∀ i, i ≠ 28 → i ≠ 29 → i ≠ 30 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
        (∀ j, 1 ≤ j → j ≤ N → i ≠ 1000+(N+1)+j) → mfin i = mem i) ∧
      mfin 28 = (N:ℤ) + 1 := by
  have h30v : Si30 mem 30 = 1000 + ((N:ℤ)+1) := by
    simp only [Si30, Function.update_self]
    rw [h31, h0]
  have h28v : Si28 (Si30 mem) 28 = (0:ℤ) + 1 := by
    have e1 : Si30 mem 3 = mem 3 := by
      simp only [Si30]; rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 30)]
    have e2 : Si30 mem 1 = mem 1 := by
      simp only [Si30]; rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 30)]
    simp only [Si28, Function.update_self]
    rw [e1, e2, h3, h1]
    norm_num
  have hpre : ∀ i, i ≠ 28 → i ≠ 30 → Si28 (Si30 mem) i = mem i := by
    intro i h28 h30
    simp only [Si28, Si30]
    rw [Function.update_of_ne h28, Function.update_of_ne h30]
  have h2s : Run Sinput 2 ⟨0, mem⟩ = ⟨2, Si28 (Si30 mem)⟩ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Run_add, Run_one, Run_one, Si0, Si1]
  have hinv : InInv r N pj 0 (Si28 (Si30 mem)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, h30v, ?_, ?_, ?_, ?_⟩
    · rw [hpre 0 (by omega) (by omega)]; exact h0
    · rw [hpre 1 (by omega) (by omega)]; exact h1
    · rw [hpre 3 (by omega) (by omega)]; exact h3
    · rw [hpre 26 (by omega) (by omega)]; exact h26
    · exact h28v
    · rw [hpre 31 (by omega) (by omega)]; exact h31
    · rw [hpre 35 (by omega) (by omega)]; exact h35
    · intro j hj1 hjN; rw [hpre (1000 + j) (by omega) (by omega)]; exact hinp j hj1 hjN
    · intro j hj1 hj0; omega
  obtain ⟨mfin, hrun, hout, hinp', h28', hfr⟩ :=
    Sinput_loop r N pj N 0 (Si28 (Si30 mem)) (Nat.zero_le _) (by omega) hinv
  refine ⟨mfin, ?_, hout, hinp', ?_, h28'⟩
  · rw [show 8*N + 3 = 2 + (8*(N-0) + 1) from by omega, Run_add, h2s, hrun]
  · intro i ha1 ha2 ha3 ha4 ha5 ha6 ha7
    rw [hfr i ha1 ha2 ha4 ha5 ha6 ha7, hpre i ha1 ha3]


-- (redundant namespace line removed)
open Nat

/-! ### Composing the setup program -/

def Sprog : List Op :=
  Sconst ++ shiftProg Sconst.length (Sdouble ++ shiftProg Sdouble.length Sinput)

theorem Sprog_length : Sprog.length = 27 := by
  rw [Sprog]
  simp [shiftProg_length, Sconst, Sdouble, Sinput]

theorem Sprog_spec (n r : ℕ) (pj : ℕ → ℕ) (m : ℕ → ℤ)
    (h0 : m 0 = (n : ℤ) + 1) (h1 : m 1 = 0) (h2 : m 2 = 1) (h3 : m 3 = 2) (h4 : m 4 = 1000)
    (h25 : m 25 = (r : ℤ)) (hinp : ∀ j, 1 ≤ j → j ≤ n → m (1000 + j) = (pj j : ℤ)) :
    ∃ mfin, Run Sprog (4*r + 8*n + 17) ⟨0, m⟩ = ⟨27, mfin⟩ ∧
      mfin 2 = 0 ∧ mfin 3 = 1 ∧ mfin 4 = 2 ∧ mfin 5 = 3 ∧ mfin 6 = 4 ∧ mfin 7 = 5 ∧
      mfin 11 = 0 ∧ mfin 12 = 0 ∧ mfin 23 = 0 ∧ mfin 25 = (r : ℤ) ∧ mfin 26 = (2:ℤ)^r ∧
      (∀ j, 1 ≤ j → j ≤ n → mfin (1000 + j) = (pj j : ℤ)) ∧
      (∀ j, 1 ≤ j → j ≤ n → mfin (1000 + (n+1) + j) = (2:ℤ)^r - (pj j : ℤ)) ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 11 → i ≠ 12 → i ≠ 23 →
        i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → i ≠ 30 → i ≠ 31 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
        i ≠ 35 → (∀ j, 1 ≤ j → j ≤ n → i ≠ 1000 + (n+1) + j) → mfin i = m i) := by
  obtain ⟨hc2, hc3, hc4, hc5, hc6, hc7, hc11, hc12, hc23, hc31, hc26, hc27, hc35, hcfr⟩ :=
    Sconst_consts n r m h1 h2 h0 h3 h4
  have hcf1 : ∀ i, i ≤ 1 → (mc m) i = m i := fun i _ => hcfr i (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hcf25 : (mc m) 25 = m 25 := hcfr 25 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcfj : ∀ j, (mc m) (1000 + j) = m (1000 + j) := fun j => hcfr (1000+j) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hcm25 : (mc m) 25 = (r : ℤ) := by rw [hcf25, h25]
  obtain ⟨mD, hD, hD26, hD27, hDfr⟩ :=
    Sdouble_run r (mc m) r hcm25 (by rw [hc27]; ring) hc3
  have hD0 : mD 0 = (n : ℤ) + 1 := by rw [hDfr 0 (by decide) (by decide), hcf1 0 (by omega), h0]
  have hD1 : mD 1 = 0 := by rw [hDfr 1 (by decide) (by decide), hcf1 1 (by omega), h1]
  have hD3 : mD 3 = 1 := by rw [hDfr 3 (by decide) (by decide), hc3]
  have hD31 : mD 31 = 1000 := by rw [hDfr 31 (by decide) (by decide), hc31]
  have hD35 : mD 35 = (n : ℤ) := by rw [hDfr 35 (by decide) (by decide), hc35]
  have hD26' : mD 26 = (2 : ℤ)^r := by rw [hD26, hc26]; ring
  have hDinj : ∀ j, 1 ≤ j → j ≤ n → mD (1000 + j) = (pj j : ℤ) := by
    intro j hj1 hjN
    rw [hDfr (1000+j) (by omega) (by omega), hcfj j]
    exact hinp j hj1 hjN
  obtain ⟨mfin, hSi, hSiA, hSiB, hSiC, hSiD⟩ :=
    Sinput_run r n pj mD hD0 hD1 hD3 hD31 hD35 hD26' hDinj
  have hRun : Run Sprog (4*r + 8*n + 17) ⟨0, m⟩ = ⟨27, mfin⟩ := by
    have hpcsd : ∀ t < 4*r + 1, (Run Sdouble t ⟨0, mc m⟩).pc < 4 :=
      fun t ht => Sdouble_pc_lt (mc m) r hc27 hcm25 hc3 t ht
    have hhit : (Run Sdouble (4*r + 1) ⟨0, mc m⟩).pc = Sdouble.length :=
      congrArg State.pc hD
    have h1 := Run_concat Sconst (Sdouble ++ shiftProg Sdouble.length Sinput) 13
      ((4*r + 1) + (8*n + 3)) ⟨0, m⟩
      (fun t ht => by
        rw [Sconst_pc m t (by omega), show Sconst.length = 13 from rfl]; omega)
      (Sconst_pc m 13 le_rfl : (Run Sconst 13 ⟨0, m⟩).pc = Sconst.length)
    have h2 := Run_concat Sdouble Sinput (4*r + 1) (8*n + 3) ⟨0, mc m⟩ hpcsd hhit
    rw [Sconst_run] at h1
    rw [h2] at h1
    rw [hD, hSi] at h1
    rw [show (13 : ℕ) + ((4*r + 1) + (8*n + 3)) = 4*r + 8*n + 17 from by ring] at h1
    rw [show Sprog = Sconst ++ shiftProg Sconst.length (Sdouble ++ shiftProg Sdouble.length Sinput)
      from rfl]
    exact h1
  have hfr2 : ∀ i, i ≤ 25 → mfin i = (mc m) i := by
    intro i hi
    rw [hSiC i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro j _ _; omega),
      hDfr i (by omega) (by omega)]
  refine ⟨mfin, hRun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hSiB, hSiA, ?_⟩
  · rw [hfr2 2 (by omega), hc2]
  · rw [hfr2 3 (by omega), hc3]
  · rw [hfr2 4 (by omega), hc4]
  · rw [hfr2 5 (by omega), hc5]
  · rw [hfr2 6 (by omega), hc6]
  · rw [hfr2 7 (by omega), hc7]
  · rw [hfr2 11 (by omega), hc11]
  · rw [hfr2 12 (by omega), hc12]
  · rw [hfr2 23 (by omega), hc23]
  · rw [hfr2 25 (by omega), hcm25]
  · rw [hSiC 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro j _ _; omega), hD26']
  · intro i hi2 hi3 hi4 hi5 hi6 hi7 hi11 hi12 hi23 hi26 hi27 hi28 hi29 hi30 hi31 hi32 hi33 hi34 hi35 hij
    rw [hSiC i hi28 hi29 hi30 hi32 hi33 hi34 hij, hDfr i hi26 hi27]
    exact hcfr i hi2 hi3 hi4 hi5 hi6 hi7 hi11 hi12 hi23 hi26 hi27 hi31 hi35


-- (redundant namespace line removed)
open Nat

/-! ### The register list of the logarithms and the selection program -/

/-- For each `j = 1..n` the two logarithms: of the prime `p_j` (register `1000+j`) and of its
negation `2^r - p_j` (register `1000+(n+1)+j`). -/
def inpListAux (n : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | (i+1) => inpListAux n i ++
      [(1000 + (i+1), 1000 + 2*(n+1) + (i+1)), (1000 + (n+1) + (i+1), 1000 + 3*(n+1) + (i+1))]

def inpList (n : ℕ) : List (ℕ × ℕ) := inpListAux n n

theorem inpListAux_mem {n i : ℕ} (hi : i ≤ n) {p : ℕ × ℕ} (hp : p ∈ inpListAux n i) :
    ∃ j, 1 ≤ j ∧ j ≤ i ∧
      (p = (1000 + j, 1000 + 2*(n+1) + j) ∨ p = (1000 + (n+1) + j, 1000 + 3*(n+1) + j)) := by
  induction i with
  | zero => simp [inpListAux] at hp
  | succ i ih =>
    rw [inpListAux] at hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨j, hj1, hji, hj⟩ := ih (by omega) h
      exact ⟨j, hj1, by omega, hj⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨i+1, by omega, by omega, Or.inl rfl⟩
      · exact ⟨i+1, by omega, by omega, Or.inr rfl⟩

theorem inpList_mem {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ inpList n) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧
      (p = (1000 + j, 1000 + 2*(n+1) + j) ∨ p = (1000 + (n+1) + j, 1000 + 3*(n+1) + j)) :=
  inpListAux_mem le_rfl hp

theorem inpListAux_nodup (n : ℕ) : ∀ i, i ≤ n → (inpListAux n i).Nodup := by
  intro i
  induction i with
  | zero => intro _; simp [inpListAux]
  | succ i ih =>
    intro hi
    rw [inpListAux, List.nodup_append]
    refine ⟨ih (by omega), by simp, ?_⟩
    intro a ha b hb
    obtain ⟨j, hj1, hji, hj⟩ := inpListAux_mem (by omega) ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega
    · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

theorem inpList_nodup (n : ℕ) : (inpList n).Nodup := inpListAux_nodup n n le_rfl

theorem inpList_length (n : ℕ) : (inpList n).length = 2*n := by
  have : ∀ i, i ≤ n → (inpListAux n i).length = 2*i := by
    intro i
    induction i with
    | zero => intro _; simp [inpListAux]
    | succ i ih => intro hi; rw [inpListAux, List.length_append, ih (by omega)]; simp; omega
  rw [inpList]; exact this n le_rfl


-- (redundant namespace line removed)
open Nat

def SelAux (n : ℕ) : ℕ → List Op
  | 0 => []
  | (i+1) => SelAux n i ++ shiftProg (SelAux n i).length
      [Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 2*(n+1) + (i+1)) (1000 + 3*(n+1) + (i+1)),
       Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 4*(n+1) + (i+1)) 3]

def Sel (n : ℕ) : List Op := SelAux n n

theorem SelAux_length (n : ℕ) : ∀ i, (SelAux n i).length = 2*i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show SelAux n (i+1) = SelAux n i ++ shiftProg (SelAux n i).length
      [Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 2*(n+1) + (i+1)) (1000 + 3*(n+1) + (i+1)),
       Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 4*(n+1) + (i+1)) 3] from rfl,
      List.length_append, ih, shiftProg_length]
    simp
    ring

theorem Run_nil (t : ℕ) (s : State) : Run [] t s = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Run_succ, ih]; rfl

theorem Run_two (P : List Op) (s : State) : Run P 2 s = stepP P (stepP P s) := by
  rw [show (2:ℕ) = 1 + 1 from rfl, Run_add, Run_one, Run_one]

theorem update_update_same {f : ℕ → ℤ} {a : ℕ} {x y : ℤ} :
    Function.update (Function.update f a x) a y = Function.update f a y := by
  funext i
  by_cases h : i = a
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]

theorem Run_append_shift0 (pre P2 : List Op) (d : ℕ) (mm : ℕ → ℤ) :
    Run (pre ++ shiftProg pre.length P2) d ⟨pre.length, mm⟩
      = ⟨pre.length + (Run P2 d ⟨0, mm⟩).pc, (Run P2 d ⟨0, mm⟩).mem⟩ := by
  induction d generalizing mm with
  | zero => simp
  | succ d ih =>
    rw [Run_succ, ih, Run_succ, stepP_append_shift]

theorem SelAux_pc (n : ℕ) (m : ℕ → ℤ) :
    ∀ i t, t ≤ (SelAux n i).length → (Run (SelAux n i) t ⟨0, m⟩).pc = t := by
  intro i
  induction i with
  | zero =>
    intro t ht
    rw [show SelAux n 0 = [] from rfl, List.length_nil] at ht
    rw [show SelAux n 0 = [] from rfl, Run_nil]
    show (0:ℕ) = t
    omega
  | succ i ih =>
    intro t ht
    set L : List Op := [Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 2*(n+1) + (i+1)) (1000 + 3*(n+1) + (i+1)),
       Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 4*(n+1) + (i+1)) 3] with hL
    have hlen : (SelAux n (i+1)).length = (SelAux n i).length + 2 := by
      rw [show SelAux n (i+1) = SelAux n i ++ shiftProg (SelAux n i).length L from rfl,
        List.length_append, shiftProg_length]; rfl
    have hUnfold : SelAux n (i+1) = SelAux n i ++ shiftProg (SelAux n i).length L := rfl
    by_cases h : t ≤ (SelAux n i).length
    · rw [hUnfold, Run_prefix (SelAux n i) (shiftProg (SelAux n i).length L)
        ((SelAux n i).length) ⟨0,m⟩
        (fun s hs => by rw [ih s (le_of_lt hs)]; exact hs) t h]
      exact ih t h
    · have ht' : t = (SelAux n i).length + (t - (SelAux n i).length) := by omega
      have hpre : Run (SelAux n i ++ shiftProg (SelAux n i).length L) ((SelAux n i).length) ⟨0, m⟩
          = ⟨(SelAux n i).length, (Run (SelAux n i) ((SelAux n i).length) ⟨0, m⟩).mem⟩ := by
        rw [Run_prefix (SelAux n i) (shiftProg (SelAux n i).length L) ((SelAux n i).length) ⟨0,m⟩
          (fun s hs => by rw [ih s (le_of_lt hs)]; exact hs) ((SelAux n i).length) le_rfl]
        exact state_pc_eq (ih ((SelAux n i).length) le_rfl)
      set d := t - (SelAux n i).length with hd
      have hd2 : d ≤ 2 := by rw [hlen] at ht; omega
      rw [hUnfold, ht', Run_add, hpre]
      rw [Run_append_shift0 (SelAux n i) L d (Run (SelAux n i) ((SelAux n i).length) ⟨0, m⟩).mem]
      interval_cases d
      · rfl
      · rfl
      · rfl

theorem SelAux_step (n i : ℕ) (mm : ℕ → ℤ) :
    Run [Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 2*(n+1) + (i+1)) (1000 + 3*(n+1) + (i+1)),
         Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 4*(n+1) + (i+1)) 3] 2 ⟨0, mm⟩
      = ⟨2, Function.update mm (1000 + 4*(n+1) + (i+1))
          (mm (1000 + 2*(n+1) + (i+1)) + mm (1000 + 3*(n+1) + (i+1)) + mm 3)⟩ := by
  rw [Run_two]
  simp only [stepP, Op.exec, List.getElem?_cons_zero, List.getElem?_cons_succ,
    update_update_same, Function.update_self,
    Function.update_of_ne (by omega : (3:ℕ) ≠ 1000 + 4*(n+1) + (i+1))]

theorem SelAux_spec (n : ℕ) (m : ℕ → ℤ) (h3 : m 3 = 1) :
    ∀ i, i ≤ n → ∃ mfin, Run (SelAux n i) (2*i) ⟨0, m⟩ = ⟨2*i, mfin⟩ ∧
      (∀ j, 1 ≤ j → j ≤ i →
        mfin (1000 + 4*(n+1) + j) = m (1000 + 2*(n+1) + j) + m (1000 + 3*(n+1) + j) + 1) ∧
      (∀ x, (∀ j, 1 ≤ j → j ≤ i → x ≠ 1000 + 4*(n+1) + j) → mfin x = m x) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨m, by simp [SelAux], ?_, ?_⟩
    · intro j hj1 hj0; omega
    · intro x _; rfl
  | succ i ih =>
    intro hi
    obtain ⟨m1, hrun, hout, hfr⟩ := ih (by omega)
    have hm13 : m1 3 = m 3 := hfr 3 (by intro j hj1 hji; omega)
    have hm1B : m1 (1000 + 2*(n+1) + (i+1)) = m (1000 + 2*(n+1) + (i+1)) :=
      hfr _ (by intro j hj1 hji; omega)
    have hm1C : m1 (1000 + 3*(n+1) + (i+1)) = m (1000 + 3*(n+1) + (i+1)) :=
      hfr _ (by intro j hj1 hji; omega)
    set L : List Op := [Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 2*(n+1) + (i+1)) (1000 + 3*(n+1) + (i+1)),
       Op.add (1000 + 4*(n+1) + (i+1)) (1000 + 4*(n+1) + (i+1)) 3] with hL
    set m2 : ℕ → ℤ := Function.update m1 (1000 + 4*(n+1) + (i+1))
      (m1 (1000 + 2*(n+1) + (i+1)) + m1 (1000 + 3*(n+1) + (i+1)) + m1 3) with hm2
    have hs := SelAux_step n i m1
    have hmem : (Run L 2 ⟨0, m1⟩).mem = m2 := by
      rw [congrArg State.mem hs]
    have hsub : Run (SelAux n i ++ shiftProg (SelAux n i).length L) (2*i + 2) ⟨0, m⟩
        = ⟨2*i + 2, m2⟩ := by
      rw [Run_concat (SelAux n i) L (2*i) 2 ⟨0, m⟩
        (by intro t ht; rw [SelAux_pc n m i t (by rw [SelAux_length]; omega), SelAux_length]; omega)
        (by rw [SelAux_pc n m i (2*i) (by rw [SelAux_length]), SelAux_length])]
      rw [hrun]
      rw [show (Run L 2 ⟨0, m1⟩).pc = 2 from congrArg State.pc hs, hmem, SelAux_length]
    refine ⟨m2, ?_, ?_, ?_⟩
    · rw [show SelAux n (i+1) = SelAux n i ++ shiftProg (SelAux n i).length L from rfl,
        show 2*(i+1) = 2*i + 2 from by ring]
      exact hsub
    · intro j hj1 hji
      rcases Nat.lt_or_ge j (i+1) with hj | hj
      · have hj' : j ≤ i := by omega
        rw [hm2, Function.update_of_ne (by omega : (1000 + 4*(n+1) + j) ≠ 1000 + 4*(n+1) + (i+1))]
        exact hout j hj1 hj'
      · have hje : j = i + 1 := by omega
        subst hje
        rw [hm2, Function.update_self, hm1B, hm1C, hm13, h3]
    · intro x hx
      rw [hm2, Function.update_of_ne (hx (i+1) (by omega) (by omega))]
      exact hfr x (by intro j hj1 hji; exact hx j hj1 (by omega))

theorem Sel_spec (n : ℕ) (m : ℕ → ℤ) (h3 : m 3 = 1) :
    ∃ mfin, Run (Sel n) (2*n) ⟨0, m⟩ = ⟨2*n, mfin⟩ ∧
      (∀ j, 1 ≤ j → j ≤ n →
        mfin (1000 + 4*(n+1) + j) = m (1000 + 2*(n+1) + j) + m (1000 + 3*(n+1) + j) + 1) ∧
      (∀ x, (∀ j, 1 ≤ j → j ≤ n → x ≠ 1000 + 4*(n+1) + j) → mfin x = m x) :=
  SelAux_spec n m h3 n le_rfl


end BkSet.RAM

end


-- ===============================================================================================
-- ============  Section `Theorem1Final` - operation cost of constructing H[n,k]  ================
-- ===============================================================================================

section

/-
# The fully merged algorithm of Theorem 1

This module assembles the two halves proved in `Theorem1` / `Theorem1Main`
(the prime generator of `PrimeGen` and the `N`-fold discrete logarithm routine) into
the single RAM program of **Theorem 1** of `AI_Bkset.pdf`, and proves

* **correctness**: for every `i = 1..n` the output register `1000 + 4*(n+1) + i` holds the
  canonical exponent `h_i` of `H[n,k]` (so the set computed is exactly `H[n,k]`), and
* **running time**: `O(n^4 + n r^2)` elementary steps,

together with the paper's amplitude bound (contents of every register stay inside
`[-1, 2^(2r) + O(1)]`).

## How the pieces are glued

The merged program is

`Th1prog n = prog.take 19 ++ shiftProg 19 (Sprog ++ shiftProg 27 (Nprog (inpList n) ++ ...))`

i.e. the prime generator cut just before its `halt`, the setup program `Sprog` (which fixes
the constant registers, computes `2^r` and stores `2^r - p_j`), the `N`-fold logarithm
routine on the `2n` inputs `p_j`, `2^r - p_j`, and the final selector `Sel n` that adds the
two logarithms and `1`.

The technical device that makes the gluing cheap is `first_hit`: each piece's specification
gives a run that *reaches* `pc = |piece|`, and `first_hit` converts it into the *first* such
time, at which the pc is known to stay strictly below `|piece|` beforehand -- exactly what
`Run_concat` needs.  `Run_concat'` packages the two together and yields the same data for the
concatenation, so the three merges are three applications of one lemma.
-/


namespace BkSet.RAM
open Nat

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## First-hit and concatenation machinery -/

/-- **First-hit lemma.**  If `P`, started from `s`, reaches pc `L` at time `T1` (with state
`⟨L, m1⟩`), `L` is absorbing for `P` (`stepP P ⟨L, _⟩ = ⟨L, _⟩`) and `L ≥ P.length - 1`
(so a pc strictly above `L` is past the end, hence stuck), then the *first* time `Tstar` at
which pc equals `L` satisfies `Tstar ≤ T1`, the pc stays strictly below `L` before `Tstar`,
and the state at `Tstar` already has the final memory `m1`. -/
theorem first_hit {P : List Op} {s : State} {T1 L : ℕ} {m1 : ℕ → ℤ}
    (hstep : ∀ m, stepP P ⟨L, m⟩ = ⟨L, m⟩)
    (hLlen : P.length ≤ L + 1)
    (hhit : Run P T1 s = ⟨L, m1⟩) :
    ∃ Tstar, Tstar ≤ T1 ∧ (∀ t < Tstar, (Run P t s).pc < L) ∧ Run P Tstar s = ⟨L, m1⟩ := by
  have hex : ∃ t, (Run P t s).pc = L := ⟨T1, by rw [hhit]⟩
  have hTle : Nat.find hex ≤ T1 := Nat.find_min' hex (by rw [hhit])
  refine ⟨Nat.find hex, hTle, ?_, ?_⟩
  · intro t ht
    have hne : (Run P t s).pc ≠ L := Nat.find_min hex ht
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt
    · exfalso
      have hge : P.length ≤ (Run P t s).pc := by omega
      have hnone : P[(Run P t s).pc]? = none := by
        rw [List.getElem?_eq_none_iff]; exact hge
      have hstuck : ∀ k, Run P k (Run P t s) = Run P t s := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [Run_succ, ih]; simp only [stepP, hnone]
      have hle : t ≤ T1 := by omega
      have hsplit : Run P T1 s = Run P (T1 - t) (Run P t s) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hle]
        rw [Run_add]
      have hcontra : L = (Run P t s).pc := by
        have h : (Run P T1 s).pc = (Run P t s).pc := by rw [hsplit, hstuck]
        rw [hhit] at h
        exact h
      omega
  · have hspec : (Run P (Nat.find hex) s).pc = L := Nat.find_spec hex
    have hsplit : Run P T1 s = Run P (T1 - Nat.find hex) (Run P (Nat.find hex) s) := by
      conv_lhs => rw [← Nat.add_sub_cancel' hTle]
      rw [Run_add]
    have hstuck : Run P (T1 - Nat.find hex) (Run P (Nat.find hex) s) = Run P (Nat.find hex) s := by
      rw [state_pc_eq hspec]
      induction (T1 - Nat.find hex) with
      | zero => simp
      | succ k ih => rw [Run_succ, ih, hstep]
    rw [hsplit, hstuck] at hhit
    exact hhit

/-- **Composition with pc tracking.**  Running `P1` (to its end, strictly below before) and
then `P2` (to its end, strictly below before) yields a run of `P1 ++ shiftProg P1.length P2`
to its own end, again strictly below before. -/
theorem Run_concat' (P1 P2 : List Op) (T1 T2 : ℕ) (s : State) (m1 m2 : ℕ → ℤ)
    (hpc1 : ∀ t < T1, (Run P1 t s).pc < P1.length)
    (h1 : Run P1 T1 s = ⟨P1.length, m1⟩)
    (hpc2 : ∀ t < T2, (Run P2 t ⟨0, m1⟩).pc < P2.length)
    (h2 : Run P2 T2 ⟨0, m1⟩ = ⟨P2.length, m2⟩) :
    (∀ t < T1 + T2,
        (Run (P1 ++ shiftProg P1.length P2) t s).pc < (P1 ++ shiftProg P1.length P2).length) ∧
      Run (P1 ++ shiftProg P1.length P2) (T1 + T2) s
        = ⟨(P1 ++ shiftProg P1.length P2).length, m2⟩ := by
  have hlen : (P1 ++ shiftProg P1.length P2).length = P1.length + P2.length := by
    rw [List.length_append, shiftProg_length]
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases lt_or_ge t T1 with hlt | hge
    · have hp := Run_prefix P1 (shiftProg P1.length P2) T1 s hpc1 t (by omega)
      rw [hp]; rw [hlen]; exact lt_of_lt_of_le (hpc1 t hlt) (Nat.le_add_right _ _)
    · have hsplit : Run (P1 ++ shiftProg P1.length P2) t s
          = Run (P1 ++ shiftProg P1.length P2) (t - T1)
              (Run (P1 ++ shiftProg P1.length P2) T1 s) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hge]
        rw [Run_add]
      have hT1 : Run (P1 ++ shiftProg P1.length P2) T1 s = ⟨P1.length, m1⟩ := by
        rw [Run_prefix P1 (shiftProg P1.length P2) T1 s hpc1 T1 le_rfl, h1]
      rw [hsplit, hT1]
      have hq : (⟨P1.length, m1⟩ : State) = ⟨P1.length + 0, m1⟩ := rfl
      rw [hq, Run_append_shift, hlen]
      exact Nat.add_lt_add_left (hpc2 (t - T1) (by omega)) _
  · have hrun := Run_concat P1 P2 T1 T2 s hpc1 (by rw [h1])
    rw [h1, h2] at hrun
    rw [hrun, List.length_append, shiftProg_length]

theorem stepP_self_len (P : List Op) (m : ℕ → ℤ) : stepP P ⟨P.length, m⟩ = ⟨P.length, m⟩ := by
  have h : P[P.length]? = none := List.getElem?_length P
  simp only [stepP, h]

theorem take19_len : (prog.take 19).length = 19 := by simp [prog]

theorem Sel_length (n : ℕ) : (Sel n).length = 2 * n := SelAux_length n n

/-! ## First-hit specifications of the three pieces -/

/-- The prime generator cut at its `halt`, run to the *first* hit of pc `19`, together with
the memory content proved in `prime_part`. -/
theorem first_part (n r : ℕ) :
    ∃ T ≤ 700 * (n + 2)^4 + 100, ∃ mem : ℕ → ℤ,
      Run (prog.take 19) T ⟨0, Function.update (initMem (n+1)) 25 (r:ℤ)⟩ = ⟨19, mem⟩ ∧
      (∀ t < T, (Run (prog.take 19) t ⟨0, Function.update (initMem (n+1)) 25 (r:ℤ)⟩).pc < 19) ∧
      mem 25 = (r : ℤ) ∧
      (∀ j, j < n+1 → mem (1000 + j) = (Nat.nth Nat.Prime j : ℤ)) ∧
      mem 0 = (n : ℤ) + 1 ∧ mem 1 = 0 ∧ mem 2 = 1 ∧ mem 3 = 2 ∧ mem 4 = 1000 ∧
      (∀ i, 16 ≤ i → i < 1000 → i ≠ 25 → mem i = 0) := by
  obtain ⟨T, hT, mem, hrun, h25, hout, h0, h1, h2, h3, h4, hzero⟩ := prime_part n r
  have hrun' : Run prog T ⟨0, Function.update (initMem (n+1)) 25 (r:ℤ)⟩ = ⟨19, mem⟩ := by
    rw [Run_prog]; exact hrun
  set m0 : ℕ → ℤ := Function.update (initMem (n+1)) 25 (r:ℤ) with hm0
  obtain ⟨Tstar, hTle, hlt, hstar⟩ := first_hit (P := prog) (s := ⟨0, m0⟩) (T1 := T)
    (L := 19) (m1 := mem) (fun m => st19 m) (by decide) hrun'
  have hagree : ∀ i, i < 19 → (prog.take 19)[i]? = prog[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hpref := Run_prefix_eq prog (prog.take 19) 19 Tstar ⟨0, m0⟩ hagree hlt
  have hstar' : Run (prog.take 19) Tstar ⟨0, m0⟩ = ⟨19, mem⟩ := by
    rw [hpref Tstar le_rfl]; exact hstar
  refine ⟨Tstar, by omega, mem, hstar', ?_, h25, hout, h0, h1, h2, h3, h4, hzero⟩
  intro t ht
  rw [hpref t (by omega)]
  exact hlt t ht

/-- First-hit form of `Sprog_spec`. -/
theorem Sprog_first (n r : ℕ) (pj : ℕ → ℕ) (m : ℕ → ℤ)
    (h0 : m 0 = (n : ℤ) + 1) (h1 : m 1 = 0) (h2 : m 2 = 1) (h3 : m 3 = 2) (h4 : m 4 = 1000)
    (h25 : m 25 = (r : ℤ)) (hinp : ∀ j, 1 ≤ j → j ≤ n → m (1000 + j) = (pj j : ℤ)) :
    ∃ T ≤ 4*r + 8*n + 17, ∃ mfin,
      Run Sprog T ⟨0, m⟩ = ⟨27, mfin⟩ ∧
      (∀ t < T, (Run Sprog t ⟨0, m⟩).pc < 27) ∧
      mfin 2 = 0 ∧ mfin 3 = 1 ∧ mfin 4 = 2 ∧ mfin 5 = 3 ∧ mfin 6 = 4 ∧ mfin 7 = 5 ∧
      mfin 11 = 0 ∧ mfin 12 = 0 ∧ mfin 23 = 0 ∧ mfin 25 = (r : ℤ) ∧ mfin 26 = (2:ℤ)^r ∧
      (∀ j, 1 ≤ j → j ≤ n → mfin (1000 + j) = (pj j : ℤ)) ∧
      (∀ j, 1 ≤ j → j ≤ n → mfin (1000 + (n+1) + j) = (2:ℤ)^r - (pj j : ℤ)) ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 11 → i ≠ 12 → i ≠ 23 →
        i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → i ≠ 30 → i ≠ 31 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
        i ≠ 35 → (∀ j, 1 ≤ j → j ≤ n → i ≠ 1000 + (n+1) + j) → mfin i = m i) := by
  obtain ⟨mfin, hrun, rest⟩ := Sprog_spec n r pj m h0 h1 h2 h3 h4 h25 hinp
  obtain ⟨T, hT, hlt, hhit⟩ := first_hit (P := Sprog) (s := ⟨0, m⟩) (T1 := 4*r + 8*n + 17)
    (L := 27) (m1 := mfin) (fun mm => by rw [← Sprog_length]; exact stepP_self_len Sprog mm)
    (by rw [Sprog_length]; omega) hrun
  exact ⟨T, hT, mfin, hhit, hlt, rest⟩

/-- First-hit form of `Nprog_spec`. -/
theorem Nprog_first (r : ℕ) (hr : 3 ≤ r) (L : List (ℕ × ℕ)) (m : ℕ → ℤ)
    (h25 : m 25 = (r : ℤ)) (h2 : m 2 = 0) (h3 : m 3 = 1) (h4 : m 4 = 2) (h5 : m 5 = 3)
    (h6 : m 6 = 4) (h7 : m 7 = 5) (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0)
    (hpre : ∀ p ∈ L, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25)
    (hnd : L.Nodup)
    (hdisj : ∀ p ∈ L, ∀ p' ∈ L, p.1 ≠ p'.2)
    (hdisj2 : ∀ p ∈ L, ∀ p' ∈ L, p ≠ p' → p.2 ≠ p'.2)
    (hval : ∀ p ∈ L, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m p.1 = (q : ℤ)) :
    ∃ T ≤ L.length * (18 + (40*(r+1)*(r+1)+100)), ∃ m' : ℕ → ℤ,
      Run (Nprog L) T ⟨0, m⟩ = ⟨(Nprog L).length, m'⟩ ∧
      (∀ t < T, (Run (Nprog L) t ⟨0, m⟩).pc < (Nprog L).length) ∧
      (∀ p ∈ L, ∀ q : ℕ, Odd q → 1 ≤ q → q < 2^r → m p.1 = (q : ℤ) → LogSpec r q (m' p.2)) ∧
      (∀ i, 25 ≤ i → (∀ p ∈ L, i ≠ p.2) → m' i = m i) ∧
      (m' 2 = 0 ∧ m' 3 = 1 ∧ m' 4 = 2 ∧ m' 5 = 3 ∧ m' 6 = 4 ∧ m' 7 = 5 ∧ m' 11 = 0 ∧
        m' 12 = 0 ∧ m' 23 = 0) := by
  obtain ⟨T0, hT0, m', hrun, rest⟩ := Nprog_spec r hr L m h25 h2 h3 h4 h5 h6 h7 h11 h12 h23
    hpre hnd hdisj hdisj2 hval
  obtain ⟨T, hT, hlt, hhit⟩ := first_hit (P := Nprog L) (s := ⟨0, m⟩) (T1 := T0)
    (L := (Nprog L).length) (m1 := m') (fun mm => stepP_self_len (Nprog L) mm) (by omega) hrun
  exact ⟨T, by omega, m', hhit, hlt, rest⟩

/-- First-hit form of `Sel_spec`. -/
theorem Sel_first (n : ℕ) (m : ℕ → ℤ) (h3 : m 3 = 1) :
    ∃ T ≤ 2*n, ∃ mfin, Run (Sel n) T ⟨0, m⟩ = ⟨2*n, mfin⟩ ∧
      (∀ t < T, (Run (Sel n) t ⟨0, m⟩).pc < 2*n) ∧
      (∀ j, 1 ≤ j → j ≤ n →
        mfin (1000 + 4*(n+1) + j) = m (1000 + 2*(n+1) + j) + m (1000 + 3*(n+1) + j) + 1) ∧
      (∀ x, (∀ j, 1 ≤ j → j ≤ n → x ≠ 1000 + 4*(n+1) + j) → mfin x = m x) := by
  obtain ⟨mfin, hrun, rest⟩ := Sel_spec n m h3
  obtain ⟨T, hT, hlt, hhit⟩ := first_hit (P := Sel n) (s := ⟨0, m⟩) (T1 := 2*n)
    (L := 2*n) (m1 := mfin) (fun mm => by rw [← Sel_length n]; exact stepP_self_len (Sel n) mm)
    (by rw [Sel_length]; omega) hrun
  exact ⟨T, hT, mfin, hhit, hlt, rest⟩

end BkSet.RAM

namespace BkSet.RAM
open Nat

/-! ## The merged program -/

/-- The logarithm half: the `N`-fold discrete logarithm on `inpList n`, followed by the
selector `Sel n`. -/
def x1 (n : ℕ) : List Op := Nprog (inpList n) ++ shiftProg (Nprog (inpList n)).length (Sel n)

/-- The setup program glued in front of the logarithm half. -/
def x2 (n : ℕ) : List Op := Sprog ++ shiftProg Sprog.length (x1 n)

/-- **The program of Theorem 1**: the prime generator (cut before its `halt`), the setup,
the `2n` discrete logarithms and the final selector. -/
def Th1prog (n : ℕ) : List Op := prog.take 19 ++ shiftProg 19 (x2 n)

/-- Initial memory of the merged program: encode `n` in register `0` and the modulus exponent
`r` in register `25` (the memory the prime generator expects, with `r` stored aside). -/
def m0 (n r : ℕ) : ℕ → ℤ := Function.update (initMem (n+1)) 25 (r : ℤ)

/-! ## Disjointness of the `2n` input/output registers -/

theorem inpList_disj {n : ℕ} {p p' : ℕ × ℕ} (hp : p ∈ inpList n) (hp' : p' ∈ inpList n) :
    p.1 ≠ p'.2 := by
  obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
  obtain ⟨j', hj1', hj'n, hj'⟩ := inpList_mem hp'
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp <;> omega

theorem inpList_disj2 {n : ℕ} {p p' : ℕ × ℕ} (hp : p ∈ inpList n) (hp' : p' ∈ inpList n)
    (hne : p ≠ p') : p.2 ≠ p'.2 := by
  intro h
  obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
  obtain ⟨j', hj1', hj'n, hj'⟩ := inpList_mem hp'
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne (by rw [show j = j' from by omega])
  · omega
  · omega
  · exact hne (by rw [show j = j' from by omega])

/-- The prime `p_j = nth Prime j` is odd, `≥ 3` and below `2^r` in range. -/
theorem nth_prime_odd_lt {j : ℕ} (hj : 1 ≤ j) :
    Odd (Nat.nth Nat.Prime j) ∧ 1 ≤ Nat.nth Nat.Prime j := by
  have heq : Nat.nth Nat.Prime j = BkSet.oddPrime (j-1) := by
    simp only [BkSet.oddPrime]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [heq]; exact BkSet.oddPrime_odd (j-1)
  · rw [heq]; have := BkSet.three_le_oddPrime (j-1); omega

theorem even_two_pow (r : ℕ) (hr : 1 ≤ r) : Even (2^r) := by
  have : 0 < r := hr
  rw [Nat.even_pow]; exact ⟨even_two, by omega⟩

/-- `2^r - p` is odd when `p` is an odd number `≤ 2^r`. -/
theorem odd_two_pow_sub {r p : ℕ} (hr : 1 ≤ r) (hp : Odd p) (hp2 : p ≤ 2^r) :
    Odd (2^r - p) :=
  Nat.Even.sub_odd hp2 (even_two_pow r hr) hp

/-- Evaluation of the output of the selector from the two logarithm specifications. -/
theorem out_eq_hh (r : ℕ) (hr : 2 ≤ r) (i : ℕ) (o1 o2 : ℤ)
    (hp : BkSet.oddPrime i ≤ 2^r)
    (h1 : LogSpec r (BkSet.oddPrime i) o1)
    (h2 : LogSpec r (2^r - BkSet.oddPrime i) o2) :
    o1 + o2 + 1 = ((BkSet.hh r hr i : ℕ) : ℤ) := by
  have hhlt : (BkSet.hh r hr i : ℕ) < 2^(r-2) := (BkSet.hh r hr i).isLt
  have hrepr := BkSet.oddPrime_repr r hr i
  have hnat : ((2^r - BkSet.oddPrime i : ℕ) : ZMod (2^r)) = -((BkSet.oddPrime i : ℕ) : ZMod (2^r)) :=
    natCast_sub_two_pow r (BkSet.oddPrime i) hp
  have hcast : ∀ q : ℕ, ((q : ℤ) : ZMod (2^r)) = ((q : ℕ) : ZMod (2^r)) := by
    intro q; push_cast; ring
  rcases Nat.lt_or_ge (BkSet.jj r hr i : ℕ) 1 with hj0 | hj1
  · have hj : (BkSet.jj r hr i : ℕ) = 0 := by omega
    have h5 : ((BkSet.oddPrime i : ℕ) : ZMod (2^r)) = (5 : ZMod (2^r))^(BkSet.hh r hr i : ℕ) := by
      rw [hrepr, hj, pow_zero, one_mul]
    have ho1 : o1 = ((BkSet.hh r hr i : ℕ) : ℤ) :=
      logspec_unique r hr (BkSet.oddPrime i) (BkSet.hh r hr i : ℕ) o1 hhlt
        (by rw [hcast, h5]) h1
    have ho2 : o2 = -1 :=
      logspec_neg r hr (2^r - BkSet.oddPrime i) (BkSet.hh r hr i : ℕ) o2 hhlt
        (by rw [hcast, hnat, h5]) h2
    rw [ho1, ho2]; ring
  · have hj : (BkSet.jj r hr i : ℕ) = 1 := by
      have := (BkSet.jj r hr i).isLt; omega
    have h5 : ((BkSet.oddPrime i : ℕ) : ZMod (2^r)) = -((5 : ZMod (2^r))^(BkSet.hh r hr i : ℕ)) := by
      rw [hrepr, hj, pow_one, neg_one_mul]
    have ho1 : o1 = -1 :=
      logspec_neg r hr (BkSet.oddPrime i) (BkSet.hh r hr i : ℕ) o1 hhlt
        (by rw [hcast, h5]) h1
    have ho2 : o2 = ((BkSet.hh r hr i : ℕ) : ℤ) :=
      logspec_unique r hr (2^r - BkSet.oddPrime i) (BkSet.hh r hr i : ℕ) o2 hhlt
        (by rw [hcast, hnat, h5, neg_neg]) h2
    rw [ho1, ho2]; ring

end BkSet.RAM

namespace BkSet.RAM
open Nat

/-! ## Membership of the individual register pairs -/

theorem inpList_mem_first {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (1000 + j, 1000 + 2*(n+1) + j) ∈ inpList n := by
  have key : ∀ i, j ≤ i → i ≤ n → (1000 + j, 1000 + 2*(n+1) + j) ∈ inpListAux n i := by
    intro i
    induction i with
    | zero => intro hji _; exfalso; omega
    | succ i ih =>
      intro hji hin
      rw [inpListAux]
      rcases Nat.lt_or_ge j (i+1) with hj | hj
      · exact List.mem_append_left _ (ih (by omega) (by omega))
      · have hje : j = i + 1 := by omega
        subst hje
        exact List.mem_append_right _ (by simp)
  rw [inpList]; exact key n hjn le_rfl

theorem inpList_mem_second {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (1000 + (n+1) + j, 1000 + 3*(n+1) + j) ∈ inpList n := by
  have key : ∀ i, j ≤ i → i ≤ n →
      (1000 + (n+1) + j, 1000 + 3*(n+1) + j) ∈ inpListAux n i := by
    intro i
    induction i with
    | zero => intro hji _; exfalso; omega
    | succ i ih =>
      intro hji hin
      rw [inpListAux]
      rcases Nat.lt_or_ge j (i+1) with hj | hj
      · exact List.mem_append_left _ (ih (by omega) (by omega))
      · have hje : j = i + 1 := by omega
        subst hje
        exact List.mem_append_right _ (by simp)
  rw [inpList]; exact key n hjn le_rfl

theorem oddPrime_lt_two_rOf (n k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i < n) :
    BkSet.oddPrime i < 2 ^ BkSet.rOf n k := by
  have hb := BkSet.rOf_bound n k hk
  have hle : BkSet.oddPrime i ≤ BkSet.oddPrime (n-1) := BkSet.oddPrime_le hi
  have h1 : 1 ≤ BkSet.oddPrime (n-1) := by have := BkSet.three_le_oddPrime (n-1); omega
  have h2 : BkSet.oddPrime (n-1) ≤ BkSet.oddPrime (n-1)^k := le_self_pow h1 (by omega)
  have h3 : 2^(BkSet.rOf n k - 1) ≤ 2^(BkSet.rOf n k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  omega

/-! ## The assembled run -/

theorem Th1_aux (n r : ℕ) (hr : 3 ≤ r)
    (hpr : ∀ j, 1 ≤ j → j ≤ n → Nat.nth Nat.Prime j < 2^r) :
    ∃ TA TB TC TD : ℕ, ∃ mD : ℕ → ℤ,
      Run (Th1prog n) (TA + (TB + (TC + TD))) ⟨0, m0 n r⟩ = ⟨(Th1prog n).length, mD⟩ ∧
      TA ≤ 700 * (n + 2)^4 + 100 ∧ TB ≤ 4*r + 8*n + 17 ∧
      TC ≤ (inpList n).length * (18 + (40*(r+1)*(r+1) + 100)) ∧ TD ≤ 2*n ∧
      (∀ j, 1 ≤ j → j ≤ n → LogSpec r (Nat.nth Nat.Prime j) (mD (1000 + 2*(n+1) + j))) ∧
      (∀ j, 1 ≤ j → j ≤ n → LogSpec r (2^r - Nat.nth Nat.Prime j) (mD (1000 + 3*(n+1) + j))) ∧
      (∀ j, 1 ≤ j → j ≤ n → mD (1000 + 4*(n+1) + j) =
        mD (1000 + 2*(n+1) + j) + mD (1000 + 3*(n+1) + j) + 1) := by
  obtain ⟨TA, hTA, mA, hA, hpcA, hA25, hAout, hA0, hA1, hA2, hA3, hA4, hAz⟩ := first_part n r
  set pj : ℕ → ℕ := fun j => Nat.nth Nat.Prime j with hpj
  obtain ⟨TB, hTB, mB, hB, hpcB, hB2, hB3, hB4, hB5, hB6, hB7, hB11, hB12, hB23, hB25, hB26,
      hBinp, hBneg, hBfr⟩ :=
    Sprog_first n r pj mA hA0 hA1 hA2 hA3 hA4 hA25 (fun j hj1 hjn => hAout j (by omega))
  have hBinn : ∀ j, 1 ≤ j → j ≤ n → mB (1000 + j) = (Nat.nth Nat.Prime j : ℤ) :=
    fun j hj1 hjn => hBinp j hj1 hjn
  have hBnegn : ∀ j, 1 ≤ j → j ≤ n → mB (1000 + (n+1) + j) = (2:ℤ)^r - (Nat.nth Nat.Prime j : ℤ) :=
    fun j hj1 hjn => hBneg j hj1 hjn
  obtain ⟨TC, hTC, mC, hC, hpcC, hClog, hCfr, hC2, hC3, hC4, hC5, hC6, hC7, hC11, hC12, hC23⟩ :=
    Nprog_first r hr (inpList n) mB hB25 hB2 hB3 hB4 hB5 hB6 hB7 hB11 hB12 hB23
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega, by omega⟩)
      (inpList_nodup n)
      (fun p hp p' hp' => inpList_disj hp hp')
      (fun p hp p' hp' hne => inpList_disj2 hp hp' hne)
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        have ho := (nth_prime_odd_lt hj1).1
        have h1 := (nth_prime_odd_lt hj1).2
        have hlt := hpr j hj1 hjn
        have hqle : Nat.nth Nat.Prime j ≤ 2^r := le_of_lt hlt
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Nat.nth Nat.Prime j, ho, h1, hlt, hBinn j hj1 hjn⟩
        · refine ⟨2^r - Nat.nth Nat.Prime j, odd_two_pow_sub (by omega) ho hqle, by omega,
            by omega, ?_⟩
          rw [hBnegn j hj1 hjn, Nat.cast_sub hqle]; push_cast; ring)
  obtain ⟨TD, hTD, mD, hD, hpcD, hDout, hDfr⟩ := Sel_first n mC hC3
  obtain ⟨hpcx1, hx1⟩ :=
    Run_concat' (Nprog (inpList n)) (Sel n) TC TD ⟨0, mB⟩ mC mD hpcC hC
      (fun t ht => by rw [Sel_length n]; exact hpcD t ht) (by rw [Sel_length n]; exact hD)
  obtain ⟨hpcx2, hx2⟩ :=
    Run_concat' Sprog (x1 n) TB (TC + TD) ⟨0, mA⟩ mB mD hpcB hB hpcx1 hx1
  obtain ⟨hpcT, hT⟩ :=
    Run_concat' (prog.take 19) (x2 n) TA (TB + (TC + TD)) ⟨0, m0 n r⟩ mA mD hpcA hA hpcx2 hx2
  have hT' : Run (Th1prog n) (TA + (TB + (TC + TD))) ⟨0, m0 n r⟩ = ⟨(Th1prog n).length, mD⟩ := by
    rw [Th1prog, ← take19_len]; exact hT
  have hfr2 : ∀ j, 1 ≤ j → j ≤ n → mD (1000 + 2*(n+1) + j) = mC (1000 + 2*(n+1) + j) :=
    fun j hj1 hjn => hDfr _ (fun j' _ _ => by omega)
  have hfr3 : ∀ j, 1 ≤ j → j ≤ n → mD (1000 + 3*(n+1) + j) = mC (1000 + 3*(n+1) + j) :=
    fun j hj1 hjn => hDfr _ (fun j' _ _ => by omega)
  refine ⟨TA, TB, TC, TD, mD, hT', hTA, hTB, hTC, hTD, ?_, ?_, ?_⟩
  · intro j hj1 hjn
    have hp := inpList_mem_first hj1 hjn
    have hlog := hClog _ hp (Nat.nth Nat.Prime j) (nth_prime_odd_lt hj1).1 (nth_prime_odd_lt hj1).2
      (hpr j hj1 hjn) (hBinn j hj1 hjn)
    rw [hfr2 j hj1 hjn]; exact hlog
  · intro j hj1 hjn
    have hp := inpList_mem_second hj1 hjn
    have hlt := hpr j hj1 hjn
    have h1 : 1 ≤ Nat.nth Nat.Prime j := (nth_prime_odd_lt hj1).2
    have h2r : 0 < 2^r := pow_pos (by norm_num) r
    have hqle : Nat.nth Nat.Prime j ≤ 2^r := le_of_lt hlt
    have hlog := hClog _ hp (2^r - Nat.nth Nat.Prime j)
      (odd_two_pow_sub (by omega) (nth_prime_odd_lt hj1).1 hqle)
      (by omega) (by omega)
      (by rw [Nat.cast_sub hqle, hBnegn j hj1 hjn]; push_cast; ring)
    rw [hfr3 j hj1 hjn]; exact hlog
  · intro j hj1 hjn
    rw [hDout j hj1 hjn, hfr2 j hj1 hjn, hfr3 j hj1 hjn]

end BkSet.RAM

namespace BkSet

theorem hh_proof_irrel (r : ℕ) (h1 h2 : 2 ≤ r) (i : ℕ) : hh r h1 i = hh r h2 i := by
  have h : reprData r h1 i = reprData r h2 i :=
    reprMap_injective r h1 (by rw [reprData_spec])
  exact congrArg Prod.snd h

end BkSet

namespace BkSet.RAM
open Nat

/-- **Theorem 1 of `AI_Bkset.pdf`.**  For all `n ≥ 1` and `k ≥ 2`, the merged program
`Th1prog n` runs on the integer RAM machine from the memory `m0 n r` (which encodes `n` in
register `0` and `r = 1 + ⌈k log₂ p_n⌉` in register `25`) for at most
`O(n^4) + 2n·O(r^2)` elementary steps and halts with

* register `1000 + 4*(n+1) + i` (`i = 0..n-1`) holding the canonical exponent `h_i` of the
  `i`-th odd prime, i.e. the values of `H[n,k]`,

so the program computes the set `H[n,k]`. -/
theorem theorem1 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ∃ (P : List Op) (T : ℕ) (mem : ℕ → ℤ),
      T ≤ 700 * (n + 2)^4 + 100 + (4 * BkSet.rOf n k + 8*n + 17)
          + (2*n) * (18 + (40*(BkSet.rOf n k + 1)*(BkSet.rOf n k + 1) + 100))
          + 2*n ∧
      Run P T ⟨0, m0 n (BkSet.rOf n k)⟩ = ⟨P.length, mem⟩ ∧
      (∀ i, i < n →
        mem (1000 + 4*(n+1) + (i+1)) =
          ((BkSet.hh (BkSet.rOf n k)
            (BkSet.rOf_ge_two n k (le_trans (by norm_num) hk)) i : ℕ) : ℤ)) := by
  have hr3 : 3 ≤ BkSet.rOf n k := three_le_rOf n k hk
  have hr2 : 2 ≤ BkSet.rOf n k := BkSet.rOf_ge_two n k (le_trans (by norm_num) hk)
  have hpr : ∀ j, 1 ≤ j → j ≤ n → Nat.nth Nat.Prime j < 2^(BkSet.rOf n k) := by
    intro j hj1 hjn
    have := oddPrime_lt_two_rOf n k (by omega) (j-1) (by omega)
    simpa only [BkSet.oddPrime, Nat.sub_add_cancel hj1] using this
  obtain ⟨TA, TB, TC, TD, mD, hT, hTA, hTB, hTC, hTD, hlog1, hlog2, hsum⟩ :=
    Th1_aux n (BkSet.rOf n k) hr3 hpr
  refine ⟨Th1prog n, TA + (TB + (TC + TD)), mD, ?_, hT, ?_⟩
  · have hlen : (inpList n).length = 2*n := inpList_length n
    rw [hlen] at hTC
    omega
  · intro i hi
    have hj1 : 1 ≤ i+1 := by omega
    have hjn : i+1 ≤ n := by omega
    have hp : BkSet.oddPrime i ≤ 2^(BkSet.rOf n k) := by
      have := oddPrime_lt_two_rOf n k (by omega) i hi; omega
    have hl1 : LogSpec (BkSet.rOf n k) (BkSet.oddPrime i)
        (mD (1000 + 2*(n+1) + (i+1))) := by
      simpa only [BkSet.oddPrime] using hlog1 (i+1) hj1 hjn
    have hl2 : LogSpec (BkSet.rOf n k) (2^(BkSet.rOf n k) - BkSet.oddPrime i)
        (mD (1000 + 3*(n+1) + (i+1))) := by
      simpa only [BkSet.oddPrime] using hlog2 (i+1) hj1 hjn
    rw [hsum (i+1) hj1 hjn]
    exact out_eq_hh (BkSet.rOf n k) hr2 i _ _ hp hl1 hl2

/-- Reformulation of `theorem1`: the values written by the program, viewed in
`ZMod (2^(r-2))`, are exactly the set `H[n,k]`. -/
theorem theorem1_Hset (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ∃ (P : List Op) (T : ℕ) (mem : ℕ → ℤ),
      T ≤ 700 * (n + 2)^4 + 100 + (4 * BkSet.rOf n k + 8*n + 17)
          + (2*n) * (18 + (40*(BkSet.rOf n k + 1)*(BkSet.rOf n k + 1) + 100))
          + 2*n ∧
      Run P T ⟨0, m0 n (BkSet.rOf n k)⟩ = ⟨P.length, mem⟩ ∧
      (Finset.range n).image
          (fun i => ((mem (1000 + 4*(n+1) + (i+1))).toNat : ZMod (2^(BkSet.rOf n k - 2))))
        = BkSet.Hset n k hk := by
  obtain ⟨P, T, mem, hT, hrun, hout⟩ := theorem1 n k hn hk
  refine ⟨P, T, mem, hT, hrun, ?_⟩
  have hz : ∀ i, i < n →
      ((mem (1000 + 4*(n+1) + (i+1))).toNat : ZMod (2^(BkSet.rOf n k - 2))) = BkSet.Hz n k hk i := by
    intro i hi
    have h := hout i hi
    have hnonneg : 0 ≤ mem (1000 + 4*(n+1) + (i+1)) := by
      rw [h]; exact Int.natCast_nonneg _
    have htoNat : (mem (1000 + 4*(n+1) + (i+1))).toNat
        = (BkSet.hh (BkSet.rOf n k)
            (BkSet.rOf_ge_two n k (le_trans (by norm_num) hk)) i : ℕ) := by
      rw [h]; simp
    rw [htoNat]
    rfl
  rw [BkSet.Hset]
  exact Finset.image_congr (fun i hi => hz i (by simpa using hi))

end BkSet.RAM

end


-- ===============================================================================================
-- = Section `Theorem1Amp` proving that register values have small enough size to leave the problem in P =
-- ===============================================================================================

section

/-
# Amplitude bound for the merged program of Theorem 1

`Theorem1Final` proves the correctness and the running time of the merged program
`Th1prog` of Theorem 1.  Theorem 1 also asserts that the
contents of every register stay inside `-1 .. 2^(2r) + O(1)` throughout the computation.
This module proves that clause, with the *same* bound `Bnd r = 2^(2r) + 2000` used in
section `RamLog`.

## The three phases

* `prime_amp`: the prime generator `prog.take 19`, whose values are at most
  `p_n + 1001 <= 2^r + 1001 <= Bnd r` (`main_bounded_all`) and are nonnegative
  (`run_nonneg`).
* `Sconst_amp`, `Sdouble_amp`, `Sinput_amp`, `Sprog_amp`: the setup program `Sprog`.  Its
  written values are the constants `1000, 2, 1, 0, 3, 4, 5`, the running counters
  `0 .. r` and `0 .. n`, `2^r`, the primes `p_j`, and `2^r - p_j`; all lie in `[-1, Bnd r]`
  since `n + 2 <= p_n < 2^r` and hence `O(n) <= 2^(2r)`.
* `Nprog_amp`, `Sel_amp`: the logarithm half (for Lemma 1, earlier in this file).

## Assembly

`Th1_aux_amp` glues the phases with `Run_concat_amp` (the amplitude-preserving form of
`Run_concat'`), and `theorem1_amp` instantiates it at `r = rOf n k`.  `theorem1_amp_n` is
the `2^(2r) + O(n)` form, and `theorem1_full` restates Theorem 1 in full (running time,
output, amplitude) in one place.
-/

namespace BkSet.RAM
open Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The explicit amplitude bound of Theorem 1: `2^(2r) + 2000`. -/
def Bnd (r : ℕ) : ℤ := (2:ℤ)^(2*r) + 2000

theorem AInv_bnd {r pc : ℕ} {mem : ℕ → ℤ} (h : AInv r pc mem) (i : ℕ) :
    -1 ≤ mem i ∧ mem i ≤ Bnd r := by
  refine ⟨?_, ?_⟩
  · by_cases hi : i = 24
    · subst hi; exact h.m24
    · exact le_trans (by norm_num : (-1:ℤ) ≤ 0) (h.nnp i hi)
  · have := h.univ i
    unfold Bnd; omega

theorem upD_lt16 (a : ℕ) (ha : a < 16) : upD a ∈ ({1,0,8,9,10,13,15,16,18,19,20,21,22,14,17,24} : Finset ℕ) := by
  interval_cases a <;> decide

theorem upD_inj16 : ∀ a, a < 16 → ∀ b, b < 16 → upD a = upD b → a = b := by
  intro a ha b hb h
  interval_cases a <;> interval_cases b <;> simp_all [upD]

theorem LinitMem_bnd (r q : ℕ) (hq : (q:ℤ) ≤ Bnd r) (hrr : (r:ℤ) ≤ Bnd r) :
    ∀ i, -1 ≤ LinitMem r q i ∧ LinitMem r q i ≤ Bnd r := by
  have h5 : (5:ℤ) ≤ Bnd r := by
    unfold Bnd
    have h2r : (0:ℤ) ≤ (2:ℤ)^(2*r) := pow_nonneg (by norm_num) _
    omega
  have hB : (0:ℤ) ≤ Bnd r := le_trans (by norm_num) h5
  intro i
  simp only [LinitMem]
  split_ifs <;>
    first
      | exact ⟨by omega, hrr⟩
      | exact ⟨by omega, hq⟩
      | exact ⟨by norm_num, by omega⟩

/-- Registers written by rprog and never written again keep their value from mstep inp 16 m. -/
theorem mstep_upD (inp k : ℕ) (hk : k ≤ 16) (m : ℕ → ℤ) {j : ℕ} (hj : j < k) :
    (mstep inp k m) (upD j) = (mstep inp 16 m) (upD j) := by
  have hj16 : j < 16 := by omega
  have hcomp : mstep inp 16 m = mrest inp k (16 - k) (mstep inp k m) := by
    rw [← mstep_compose inp k (16-k) m]; congr 1; omega
  rw [hcomp]
  exact (mrest_frame inp k (mstep inp k m) (16-k) (by omega) (upD j) (by
    intro t ht hc
    exact absurd (upD_inj16 (k+t) (by omega) j hj16 hc) (by omega))).symm

theorem mstep_bnd (r q inp : ℕ) (m : ℕ → ℤ) (hr : 1 ≤ r) (hinp : 25 ≤ inp)
    (h2 : m 2 = 0) (h3 : m 3 = 1) (h25 : m 25 = (r : ℤ)) (hinpv : m inp = (q : ℤ))
    (h4 : m 4 = 2) (h5 : m 5 = 3) (h6 : m 6 = 4) (h7 : m 7 = 5)
    (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0)
    (hq : (q:ℤ) ≤ Bnd r) (hrr : (r:ℤ) ≤ Bnd r) (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ k ≤ 16, ∀ i, -1 ≤ mstep inp k m i ∧ mstep inp k m i ≤ Bnd r := by
  intro k hk i
  by_cases hw : ∃ j, j < k ∧ upD j = i
  · obtain ⟨j, hj, rfl⟩ := hw
    rw [mstep_upD inp k hk m hj]
    have hle24 : upD j ≤ 24 := by
      have := upD_lt16 j (by omega); simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega
    rw [(rprog_spec r q inp hinp m h2 h3 h25 hinpv h4 h5 h6 h7 h11 h12 h23).2.1 (upD j) hle24]
    exact LinitMem_bnd r q hq hrr (upD j)
  · rw [mstep_frame inp m k hk i (by rintro j hj rfl; exact hw ⟨j, hj, rfl⟩)]
    exact hm i


/-! ## The tail of the logarithm program after its halting pc -/

@[simp] theorem mem_mk (pc : ℕ) (m : ℕ → ℤ) : ((⟨pc, m⟩ : State)).mem = m := rfl

theorem Ltail_stuck49 (out : ℕ) (v : ℕ → ℤ) (w : ℕ) :
    Run (Ltail out) w ⟨49, v⟩ = ⟨49, v⟩ := by
  induction w with
  | zero => rfl
  | succ w ih => rw [show (w+1 : ℕ) = w + 1 from rfl, Run_add, ih]; exact Ltail_step49 out v

theorem upd_out_self (out : ℕ) (hout : 25 ≤ out) (f : ℕ → ℤ) (hf : f out = f 24 + f 2) :
    Function.update f out (f 24 + f 2) = f := by
  funext i
  by_cases hi : i = out
  · subst hi; rw [Function.update_self, hf]
  · rw [Function.update_of_ne hi]

theorem upd24 (out : ℕ) (hout : 25 ≤ out) (mm : ℕ → ℤ) :
    Function.update (Function.update mm out (mm 24 + mm 2)) out
      ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2)
      = Function.update mm out (mm 24 + mm 2) := by
  apply upd_out_self out hout
  rw [Function.update_self, Function.update_of_ne (by omega : (24:ℕ) ≠ out),
    Function.update_of_ne (by omega : (2:ℕ) ≠ out)]

theorem Ltail_two47 (out : ℕ) (hout : 25 ≤ out) (mm : ℕ → ℤ) :
    Run (Ltail out) 2 ⟨47, mm⟩ = ⟨49, Function.update mm out (mm 24 + mm 2)⟩ := by
  rw [Run_two]
  rw [show stepP (Ltail out) ⟨47, mm⟩ = ⟨48, Function.update mm out (mm 24 + mm 2)⟩ from by
    rw [← Run_one]; exact Ltail_step47 out mm]
  rw [show stepP (Ltail out) ⟨48, Function.update mm out (mm 24 + mm 2)⟩
      = ⟨49, Function.update (Function.update mm out (mm 24 + mm 2)) out
          ((Function.update mm out (mm 24 + mm 2)) 24 + (Function.update mm out (mm 24 + mm 2)) 2)⟩ from by
    rw [← Run_one]; exact Ltail_step48 out (Function.update mm out (mm 24 + mm 2))]
  rw [upd24 out hout mm]

/-- Registers other than `out` are frozen once the logarithm program has halted. -/
theorem Ltail_hi (out : ℕ) (hout : 25 ≤ out) (mm : ℕ → ℤ) :
    (∀ u {i : ℕ}, i ≠ out → (Run (Ltail out) u ⟨47, mm⟩).mem i = mm i) ∧
    (∀ u {i : ℕ}, i ≠ out → (Run (Ltail out) u ⟨48, mm⟩).mem i = mm i) := by
  constructor
  · intro u
    rcases u with _ | _ | u
    · intro i _; rfl
    · intro i hi; rw [Ltail_step47]; exact Function.update_of_ne hi _ _
    · intro i hi
      rw [show (u+2 : ℕ) = 2 + u from by omega, Run_add, Ltail_two47 out hout mm, Ltail_stuck49]
      exact Function.update_of_ne hi _ _
  · intro u
    rcases u with _ | u
    · intro i _; rfl
    · intro i hi
      rw [show (u+1 : ℕ) = 1 + u from by omega, Run_add, Ltail_step48, Ltail_stuck49]
      exact Function.update_of_ne hi _ _

theorem Ltail_out47 (out : ℕ) (hout : 25 ≤ out) (mm : ℕ → ℤ) {u : ℕ} (hu : 1 ≤ u) :
    (Run (Ltail out) u ⟨47, mm⟩).mem out = mm 24 + mm 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u-1, by omega⟩
  rcases Nat.eq_zero_or_pos w with h0 | hpos
  · subst h0; rw [Ltail_step47]; simp
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w-1, by omega⟩
    rw [show (w'+1+1 : ℕ) = 2 + w' from by omega, Run_add, Ltail_two47 out hout mm, Ltail_stuck49]
    simp

theorem Ltail_out48 (out : ℕ) (hout : 25 ≤ out) (mm : ℕ → ℤ) {u : ℕ} (hu : 1 ≤ u) :
    (Run (Ltail out) u ⟨48, mm⟩).mem out = mm 24 + mm 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u-1, by omega⟩
  rw [show (w+1 : ℕ) = 1 + w from by omega, Run_add, Ltail_step48, Ltail_stuck49]
  simp


theorem Lrun_frame (t pc : ℕ) (mm : ℕ → ℤ) {i : ℕ} (hi : ¬ i ≤ 24) :
    (Lrun t (⟨pc, mm⟩ : State)).mem i = mm i := by
  rw [← Run_Lprog]
  exact Run_frame Lprog (fun d => d ≤ 24) Lprog_le24 (⟨pc, mm⟩ : State) t i hi

/-! ## Amplitude of one logarithm block -/

theorem blk_amp (r q : ℕ) (hr : 3 ≤ r) (hodd : Odd q) (hq1 : 1 ≤ q) (hqu : q < 2^r)
    (inp out : ℕ) (hinp : 25 ≤ inp) (hout : 25 ≤ out)
    (m : ℕ → ℤ) (h2 : m 2 = 0) (h3 : m 3 = 1) (h25 : m 25 = (r : ℤ)) (hinpv : m inp = (q : ℤ))
    (h4 : m 4 = 2) (h5 : m 5 = 3) (h6 : m 6 = 4) (h7 : m 7 = 5)
    (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0)
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run (blk inp out) t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  obtain ⟨hres, hagree, hfr16⟩ := rprog_spec r q inp hinp m h2 h3 h25 hinpv h4 h5 h6 h7 h11 h12 h23
  obtain ⟨TL, hTL, hpre, hlog⟩ := lt_log r q hr hodd hq1 hqu
  have hqle : (q:ℤ) ≤ Bnd r := by
    have h1 : (q:ℤ) < (2:ℤ)^r := by exact_mod_cast hqu
    have h2' : (2:ℤ)^r ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold Bnd; omega
  have hrr : (r:ℤ) ≤ Bnd r := by
    have h1 : (r:ℤ) < (2:ℤ)^r := by exact_mod_cast (Nat.lt_two_pow_self (n := r))
    have h2' : (2:ℤ)^r ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold Bnd; omega
  set mm0 : ℕ → ℤ := mstep inp 16 m with hmm0
  have hpcR : ∀ s < 16, (Run (rprog inp) s ⟨0, m⟩).pc < (rprog inp).length := by
    intro s hs; rw [rprog_pc inp m s (by omega), rprog_length]; omega
  have hpreL : ∀ u < TL, (Run Lprog u (⟨0, mm0⟩ : State)).pc < 47 := by
    intro u hu
    have h := (Lrun_agree u 0 mm0 (LinitMem r q) hagree).1
    rw [show (Run Lprog u (⟨0, mm0⟩ : State)).pc = (Lrun u (⟨0, mm0⟩ : State)).pc from
      congrArg State.pc (Run_Lprog u _), h]
    exact hpre u hu
  have hpref : ∀ u ≤ TL, Run (Ltail out) u (⟨0, mm0⟩ : State) = Lrun u (⟨0, mm0⟩ : State) := by
    intro u hu
    rw [Run_prefix_eq Lprog (Ltail out) 47 TL (⟨0, mm0⟩ : State)
      (fun i hi => Ltail_getElem?_lt out i hi) hpreL u hu, Run_Lprog]
  have hagreeL : ∀ t, ∀ i, i ≤ 24 → (Lrun t (⟨0, mm0⟩ : State)).mem i = (Lrun t (Ls0 r q)).mem i :=
    fun t i hi => (Lrun_agree t 0 mm0 (LinitMem r q) hagree).2 i hi
  have hpcL : ∀ t, (Lrun t (⟨0, mm0⟩ : State)).pc = (Lrun t (Ls0 r q)).pc :=
    fun t => (Lrun_agree t 0 mm0 (LinitMem r q) hagree).1
  have hATL : AInv r (Lrun TL (Ls0 r q)).pc (Lrun TL (Ls0 r q)).mem := ainv_run r q hr hq1 hqu TL _ _ rfl
  have hpce : (Lrun TL (Ls0 r q)).pc = 47 ∨ (Lrun TL (Ls0 r q)).pc = 48 := by
    rcases hlog with ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  intro t pc ms hrun i
  rcases lt_or_ge t 17 with ht | ht
  · have ht' : t ≤ 16 := by omega
    have hp := Run_prefix (rprog inp) (shiftProg 16 (Ltail out)) 16 ⟨0, m⟩ hpcR t ht'
    rw [blk] at hrun
    rw [hp, rprog_run_le inp m t ht'] at hrun
    injection hrun with _ hms
    subst hms
    exact mstep_bnd r q inp m (by omega) hinp h2 h3 h25 hinpv h4 h5 h6 h7 h11 h12 h23 hqle hrr hm t ht' i
  · have h16 : Run (blk inp out) 16 ⟨0, m⟩ = ⟨16, mm0⟩ := by
      rw [blk]
      rw [Run_prefix (rprog inp) (shiftProg 16 (Ltail out)) 16 ⟨0, m⟩ hpcR 16 le_rfl]
      exact rprog_run inp m
    have happ : Run (blk inp out) (t - 16) (⟨16, mm0⟩ : State)
        = ⟨16 + (Run (Ltail out) (t - 16) ⟨0, mm0⟩).pc,
            (Run (Ltail out) (t - 16) ⟨0, mm0⟩).mem⟩ := by
      rw [blk]
      exact Run_append_shift (rprog inp) (Ltail out) (t - 16) 0 mm0
    have hsplit : Run (blk inp out) t ⟨0, m⟩
        = Run (blk inp out) (t - 16) (Run (blk inp out) 16 ⟨0, m⟩) := by
      conv_lhs => rw [← Nat.add_sub_cancel' (by omega : 16 ≤ t)]
      rw [Run_add]
    rw [hsplit, h16, happ] at hrun
    injection hrun with _ hms
    set sg : ℕ := t - 16 with hsg
    rcases lt_or_ge sg (TL+1) with hs | hs
    · have hs' : sg ≤ TL := by omega
      rw [hpref sg hs'] at hms
      by_cases hi24 : i ≤ 24
      · rw [← hms, hagreeL sg i hi24]
        exact AInv_bnd (ainv_run r q hr hq1 hqu sg _ _ rfl) i
      · simp only [Nat.not_le] at hi24
        have h1 : (Lrun sg (⟨0, mm0⟩ : State)).mem i = mm0 i :=
          Lrun_frame sg 0 mm0 (by omega)
        rw [← hms, h1, hfr16 i (by omega)]
        exact hm i
    · have hsle : TL ≤ sg := by omega
      have hTLstate : Run (Ltail out) TL (⟨0, mm0⟩ : State)
          = ⟨(Lrun TL (Ls0 r q)).pc, (Lrun TL (⟨0, mm0⟩ : State)).mem⟩ := by
        rw [hpref TL le_rfl]
        exact state_pc_eq (hpcL TL)
      have hsplit2 : Run (Ltail out) sg (⟨0, mm0⟩ : State)
          = Run (Ltail out) (sg - TL) (Run (Ltail out) TL (⟨0, mm0⟩ : State)) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hsle]
        rw [Run_add]
      rw [hsplit2, hTLstate] at hms
      set memTL : ℕ → ℤ := (Lrun TL (⟨0, mm0⟩ : State)).mem with hmemTLdef
      have hmemTL : ∀ i, i ≤ 24 → memTL i = (Lrun TL (Ls0 r q)).mem i := hagreeL TL
      by_cases hi24 : i ≤ 24
      · rw [← hms]
        rcases hpce with h47 | h48
        · rw [h47, (Ltail_hi out hout memTL).1 (sg - TL) (by omega : i ≠ out), hmemTL i hi24]
          exact AInv_bnd hATL i
        · rw [h48, (Ltail_hi out hout memTL).2 (sg - TL) (by omega : i ≠ out), hmemTL i hi24]
          exact AInv_bnd hATL i
      · simp only [Nat.not_le] at hi24
        by_cases hio : i = out
        · rw [hio, ← hms]
          rcases Nat.eq_zero_or_pos (sg - TL) with h0 | hpos
          · rw [h0, Run_zero, mem_mk, hmemTLdef, Lrun_frame TL 0 mm0 (by omega), hfr16 out hout]
            exact hm out
          · rcases hpce with h47 | h48
            · rw [h47, Ltail_out47 out hout memTL hpos, hmemTL 24 (by omega), hmemTL 2 (by omega), hATL.c2]
              refine ⟨by have := hATL.m24; omega, ?_⟩
              have h2 := hATL.univ 24
              simp only [Bnd]
              omega
            · rw [h48, Ltail_out48 out hout memTL hpos, hmemTL 24 (by omega), hmemTL 2 (by omega), hATL.c2]
              refine ⟨by have := hATL.m24; omega, ?_⟩
              have h2 := hATL.univ 24
              simp only [Bnd]
              omega
        · rw [← hms, Run_frame (Ltail out) (fun d => d ≤ 24 ∨ d = out) (Ltail_ops out)
              ⟨(Lrun TL (Ls0 r q)).pc, memTL⟩ (sg - TL) i (by omega),
            hmemTLdef, Lrun_frame TL 0 mm0 (by omega),
            hfr16 i (by omega)]
          exact hm i


theorem logspec_bnd {r q : ℕ} {o : ℤ} (hr : 1 ≤ r) (h : LogSpec r q o) :
    -1 ≤ o ∧ o ≤ Bnd r := by
  rcases h with ⟨a, ha, _, ho⟩ | ⟨ho, _⟩
  · rw [ho]
    refine ⟨by omega, ?_⟩
    have h1 : (a:ℤ) < (2:ℤ)^(r-2) := by exact_mod_cast ha
    have h2 : (2:ℤ)^(r-2) ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [Bnd]; omega
  · rw [ho]
    refine ⟨by norm_num, ?_⟩
    simp only [Bnd]
    have : (0:ℤ) ≤ (2:ℤ)^(2*r) := pow_nonneg (by norm_num) _
    omega

/-- Amplitude of the `N`-fold logarithm routine. -/
theorem Nprog_amp (r : ℕ) (hr : 3 ≤ r) (L : List (ℕ × ℕ)) (m : ℕ → ℤ)
    (h25 : m 25 = (r : ℤ)) (h2 : m 2 = 0) (h3 : m 3 = 1) (h4 : m 4 = 2) (h5 : m 5 = 3)
    (h6 : m 6 = 4) (h7 : m 7 = 5) (h11 : m 11 = 0) (h12 : m 12 = 0) (h23 : m 23 = 0)
    (hpre : ∀ p ∈ L, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25)
    (hnd : L.Nodup)
    (hdisj : ∀ p ∈ L, ∀ p' ∈ L, p.1 ≠ p'.2)
    (hdisj2 : ∀ p ∈ L, ∀ p' ∈ L, p ≠ p' → p.2 ≠ p'.2)
    (hval : ∀ p ∈ L, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m p.1 = (q : ℤ))
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run (Nprog L) t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  induction L generalizing m with
  | nil =>
    intro t pc ms hrun i
    have h : Run (Nprog []) t ⟨0, m⟩ = ⟨0, m⟩ := by
      rw [Nprog]; exact Run_nil t ⟨0, m⟩
    rw [h] at hrun
    injection hrun with _ hms
    rw [← hms]
    exact hm i
  | cons p rest ih =>
    obtain ⟨i, o⟩ := p
    obtain ⟨hp1, hp2, hp3⟩ := hpre (i, o) (by simp)
    obtain ⟨q, hqodd, hq1, hqu, hqv⟩ := hval (i, o) (by simp)
    obtain ⟨T1, hT1, m1, hrun1, hpc1, hlog1, hframe1, hconst1⟩ :=
      blk_spec r q hr hqodd hq1 hqu i o hp1 hp2 m h25 hqv h2 h3 h4 h5 h6 h7 h11 h12 h23
    have hblk := blk_amp r q hr hqodd hq1 hqu i o hp1 hp2 m h2 h3 h25 hqv h4 h5 h6 h7 h11 h12 h23 hm
    have hm1 : ∀ i, -1 ≤ m1 i ∧ m1 i ≤ Bnd r := by
      intro i
      by_cases hi : i ≤ 24
      · exact hblk T1 65 m1 hrun1 i
      · simp only [Nat.not_le] at hi
        by_cases hio : i = o
        · subst hio; exact logspec_bnd (by omega) hlog1
        · rw [hframe1 i (by omega) hio]; exact hm i
    have hpre' : ∀ p ∈ rest, 25 ≤ p.1 ∧ 25 ≤ p.2 ∧ p.2 ≠ 25 :=
      fun p hp => hpre p (by simp only [List.mem_cons]; exact Or.inr hp)
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hdisj' : ∀ p ∈ rest, ∀ p' ∈ rest, p.1 ≠ p'.2 :=
      fun p hp p' hp' => hdisj p (by simp only [List.mem_cons]; exact Or.inr hp) p'
        (by simp only [List.mem_cons]; exact Or.inr hp')
    have hdisj2' : ∀ p ∈ rest, ∀ p' ∈ rest, p ≠ p' → p.2 ≠ p'.2 :=
      fun p hp p' hp' hne => hdisj2 p (by simp only [List.mem_cons]; exact Or.inr hp) p'
        (by simp only [List.mem_cons]; exact Or.inr hp') hne
    have hval' : ∀ p ∈ rest, ∃ q : ℕ, Odd q ∧ 1 ≤ q ∧ q < 2^r ∧ m1 p.1 = (q : ℤ) := by
      intro p hp
      obtain ⟨q', ho, h1, hu, hv⟩ := hval p (by simp only [List.mem_cons]; exact Or.inr hp)
      refine ⟨q', ho, h1, hu, ?_⟩
      rw [← hv]
      exact hframe1 p.1 (hpre p (by simp only [List.mem_cons]; exact Or.inr hp)).1
        (hdisj p (by simp only [List.mem_cons]; exact Or.inr hp) (i, o) (by simp))
    have hconst1' : m1 2 = 0 ∧ m1 3 = 1 ∧ m1 4 = 2 ∧ m1 5 = 3 ∧ m1 6 = 4 ∧
        m1 7 = 5 ∧ m1 11 = 0 ∧ m1 12 = 0 ∧ m1 23 = 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        rw [hconst1 _ (by decide)] <;>
        first | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 |
          exact h11 | exact h12 | exact h23
    have h25' : m1 25 = (r : ℤ) := by rw [hframe1 25 (by omega) hp3.symm]; exact h25
    have hih := ih m1 h25' hconst1'.1 hconst1'.2.1 hconst1'.2.2.1 hconst1'.2.2.2.1
      hconst1'.2.2.2.2.1 hconst1'.2.2.2.2.2.1 hconst1'.2.2.2.2.2.2.1 hconst1'.2.2.2.2.2.2.2.1
      hconst1'.2.2.2.2.2.2.2.2 hpre' hnd' hdisj' hdisj2' hval' hm1
    obtain ⟨Tb, hTb, hpcb, hrunb⟩ := first_hit (P := blk i o) (s := ⟨0, m⟩) (T1 := T1)
      (L := 65) (m1 := m1) (fun mm => by rw [← blk_length]; exact stepP_self_len (blk i o) mm)
      (by rw [blk_length]; omega) hrun1
    have hpcb' : ∀ s < Tb, (Run (blk i o) s ⟨0, m⟩).pc < (blk i o).length :=
      fun s hs => by rw [blk_length]; exact hpcb s hs
    intro t pc ms hrun k
    rcases lt_or_ge t Tb with ht | ht
    · have hp := Run_prefix (blk i o) (shiftProg (blk i o).length (Nprog rest)) Tb ⟨0, m⟩
        hpcb' t (by omega)
      rw [Nprog] at hrun
      rw [hp] at hrun
      exact hblk t pc ms hrun k
    · have hsplit : Run (Nprog ((i,o)::rest)) t ⟨0, m⟩
          = Run (Nprog ((i,o)::rest)) (t - Tb) (Run (Nprog ((i,o)::rest)) Tb ⟨0, m⟩) := by
        conv_lhs => rw [← Nat.add_sub_cancel' (by omega : Tb ≤ t)]
        rw [Run_add]
      have hTb' : Run (Nprog ((i,o)::rest)) Tb ⟨0, m⟩ = ⟨65, m1⟩ := by
        rw [Nprog]
        rw [Run_prefix (blk i o) (shiftProg (blk i o).length (Nprog rest)) Tb ⟨0, m⟩
          hpcb' Tb le_rfl]
        exact hrunb
      have happ : Run (Nprog ((i,o)::rest)) (t - Tb) (⟨65, m1⟩ : State)
          = ⟨65 + (Run (Nprog rest) (t - Tb) ⟨0, m1⟩).pc,
              (Run (Nprog rest) (t - Tb) ⟨0, m1⟩).mem⟩ := by
        rw [Nprog]
        exact Run_append_shift (blk i o) (Nprog rest) (t - Tb) 0 m1
      rw [hsplit, hTb', happ] at hrun
      injection hrun with _ hms
      rw [← hms]
      exact hih (t - Tb) _ _ rfl k


/-! ## Amplitude glue and the selector -/

theorem Run_concat_amp (P1 P2 : List Op) (T1 : ℕ) (s : State) (m1 : ℕ → ℤ) (r : ℕ)
    (hpc1 : ∀ t < T1, (Run P1 t s).pc < P1.length)
    (h1 : Run P1 T1 s = ⟨P1.length, m1⟩)
    (hAmp1 : ∀ t, ∀ pc ms, Run P1 t s = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r)
    (hAmp2 : ∀ t, ∀ pc ms, Run P2 t ⟨0, m1⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run (P1 ++ shiftProg P1.length P2) t s = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  intro t pc ms hrun i
  rcases lt_or_ge t T1 with ht | ht
  · have hp := Run_prefix P1 (shiftProg P1.length P2) T1 s hpc1 t (by omega)
    rw [hp] at hrun
    exact hAmp1 t pc ms hrun i
  · have hsplit : Run (P1 ++ shiftProg P1.length P2) t s
        = Run (P1 ++ shiftProg P1.length P2) (t - T1) (Run (P1 ++ shiftProg P1.length P2) T1 s) := by
      conv_lhs => rw [← Nat.add_sub_cancel' ht]
      rw [Run_add]
    have hT1 : Run (P1 ++ shiftProg P1.length P2) T1 s = ⟨P1.length, m1⟩ := by
      rw [Run_prefix P1 (shiftProg P1.length P2) T1 s hpc1 T1 le_rfl, h1]
    rw [hsplit, hT1] at hrun
    have hq : (⟨P1.length, m1⟩ : State) = ⟨P1.length + 0, m1⟩ := rfl
    rw [hq, Run_append_shift] at hrun
    injection hrun with _ hms
    rw [← hms]
    exact hAmp2 (t - T1) _ _ rfl i

theorem selblk1 (o a b : ℕ) (m : ℕ → ℤ) :
    Run [Op.add o a b, Op.add o o 3] 1 ⟨0, m⟩ = ⟨1, Function.update m o (m a + m b)⟩ := by
  rw [Run_one]
  show (match ([Op.add o a b, Op.add o o 3] : List Op)[0]? with
        | some op => op.exec (⟨0, m⟩ : State)
        | none => (⟨0, m⟩ : State)) = ⟨1, Function.update m o (m a + m b)⟩
  rw [show ([Op.add o a b, Op.add o o 3] : List Op)[0]? = some (Op.add o a b) from rfl]
  rfl

theorem selblk2 (o a b : ℕ) (h3 : o ≠ 3) (m : ℕ → ℤ) (h31 : m 3 = 1) :
    Run [Op.add o a b, Op.add o o 3] 2 ⟨0, m⟩ = ⟨2, Function.update m o (m a + m b + 1)⟩ := by
  have h2 : Run [Op.add o a b, Op.add o o 3] 1 ⟨1, Function.update m o (m a + m b)⟩
      = ⟨2, Function.update m o (m a + m b + 1)⟩ := by
    rw [Run_one]
    show (match ([Op.add o a b, Op.add o o 3] : List Op)[1]? with
          | some op => op.exec (⟨1, Function.update m o (m a + m b)⟩ : State)
          | none => (⟨1, Function.update m o (m a + m b)⟩ : State))
        = ⟨2, Function.update m o (m a + m b + 1)⟩
    rw [show ([Op.add o a b, Op.add o o 3] : List Op)[1]? = some (Op.add o o 3) from rfl]
    simp only [Op.exec]
    rw [Function.update_self, Function.update_of_ne h3.symm, h31, Function.update_idem]
  rw [show (2:ℕ) = 1 + 1 from rfl, Run_add, selblk1 o a b m, h2]

theorem selblk_stuck (o a b : ℕ) (v : ℕ → ℤ) (k : ℕ) :
    Run [Op.add o a b, Op.add o o 3] k ⟨2, v⟩ = ⟨2, v⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show (k+1 : ℕ) = k + 1 from rfl, Run_add, ih, Run_one]
    show (match ([Op.add o a b, Op.add o o 3] : List Op)[2]? with
          | some op => op.exec (⟨2, v⟩ : State)
          | none => (⟨2, v⟩ : State)) = ⟨2, v⟩
    rw [show ([Op.add o a b, Op.add o o 3] : List Op)[2]? = none from rfl]

theorem selblk_amp (r o a b : ℕ) (hr : 1 ≤ r) (m : ℕ → ℤ) (h3 : m 3 = 1)
    (ho3 : o ≠ 3) (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r)
    (ha : -1 ≤ m a + m b) (hb : m a + m b ≤ (2:ℤ)^(r-2) - 1) :
    ∀ t, ∀ pc ms, Run [Op.add o a b, Op.add o o 3] t ⟨0, m⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hle : (2:ℤ)^(r-2) ≤ Bnd r := by
    have h : (2:ℤ)^(r-2) ≤ (2:ℤ)^(2*r) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [Bnd]; omega
  intro t pc ms hrun i
  rcases Nat.lt_or_ge t 1 with h0 | h0
  · have ht0 : t = 0 := by omega
    subst ht0
    rw [Run_zero] at hrun
    injection hrun with _ hms
    rw [← hms]; exact hm i
  rcases Nat.lt_or_ge t 2 with h1 | h1
  · have ht1 : t = 1 := by omega
    subst ht1
    rw [selblk1 o a b m] at hrun
    injection hrun with _ hms
    rw [← hms]
    by_cases hio : i = o
    · subst hio; rw [Function.update_self]; exact ⟨ha, by omega⟩
    · rw [Function.update_of_ne hio]; exact hm i
  · obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    rw [show (k+2 : ℕ) = 2 + k from by omega, Run_add, selblk2 o a b ho3 m h3,
      selblk_stuck o a b _ k] at hrun
    injection hrun with _ hms
    rw [← hms]
    by_cases hio : i = o
    · subst hio; rw [Function.update_self]
      refine ⟨?_, ?_⟩
      · linarith [ha]
      · simp only [Bnd] at hle ⊢
        linarith [hb, hle]
    · rw [Function.update_of_ne hio]; exact hm i


theorem SelAux_ge (n : ℕ) : ∀ i, i ≤ n → ∀ op ∈ SelAux n i, OpLeOr (fun d => 1000 + 4*(n+1) ≤ d) op := by
  intro i
  induction i with
  | zero => intro _ op hop; simp [SelAux] at hop
  | succ i ih =>
    intro hi op hop
    rw [SelAux] at hop
    rcases List.mem_append.mp hop with h | h
    · exact ih (by omega) op h
    · simp only [shiftProg] at h
      rw [List.mem_map] at h
      obtain ⟨op', hop', rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop'
      rcases hop' with rfl | rfl <;>
        · exact OpLeOr_shiftOp (show OpLeOr (fun d => 1000 + 4*(n+1) ≤ d)
            (Op.add (1000 + 4*(n+1) + (i+1)) _ _) from by simp only [OpLeOr]; omega)

theorem SelAux_amp (n r : ℕ) (hr : 1 ≤ r) (m : ℕ → ℤ) (h3 : m 3 = 1)
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r)
    (hin : ∀ j, 1 ≤ j → j ≤ n → -1 ≤ m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ∧
      m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ≤ (2:ℤ)^(r-2) - 1) :
    ∀ i, i ≤ n → ∀ t pc ms, Run (SelAux n i) t ⟨0, m⟩ = ⟨pc, ms⟩ →
      ∀ k, -1 ≤ ms k ∧ ms k ≤ Bnd r := by
  intro i
  induction i with
  | zero =>
    intro _ t pc ms hrun k
    rw [show SelAux n 0 = ([] : List Op) from rfl, Run_nil] at hrun
    injection hrun with _ hms
    rw [← hms]; exact hm k
  | succ i ih =>
    intro hi t pc ms hrun k
    have hii : i ≤ n := by omega
    have hin' : ∀ j, 1 ≤ j → j ≤ n → -1 ≤ m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ∧
        m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ≤ (2:ℤ)^(r-2) - 1 := hin
    have hpc1 : ∀ t < 2*i, (Run (SelAux n i) t ⟨0, m⟩).pc < (SelAux n i).length := by
      intro t ht
      rw [SelAux_pc n m i t (by rw [SelAux_length]; omega), SelAux_length]
      omega
    have h1 : Run (SelAux n i) (2*i) ⟨0, m⟩ = ⟨(SelAux n i).length, (Run (SelAux n i) (2*i) ⟨0, m⟩).mem⟩ :=
      state_pc_eq (by rw [SelAux_pc n m i (2*i) (by rw [SelAux_length])]; rw [SelAux_length])
    have hAmp1 : ∀ t, ∀ pc ms, Run (SelAux n i) t ⟨0, m⟩ = ⟨pc, ms⟩ →
        ∀ k, -1 ≤ ms k ∧ ms k ≤ Bnd r := ih hii
    set mi : ℕ → ℤ := (Run (SelAux n i) (2*i) ⟨0, m⟩).mem with hmi
    have hmiB : ∀ k, -1 ≤ mi k ∧ mi k ≤ Bnd r := hAmp1 (2*i) _ _ (by rw [h1])
    have hge := SelAux_ge n i hii
    have hfrA : mi (1000+2*(n+1)+(i+1)) = m (1000+2*(n+1)+(i+1)) :=
      Run_frame (SelAux n i) (fun d => 1000+4*(n+1) ≤ d) hge ⟨0, m⟩ (2*i) _ (by omega)
    have hfrB : mi (1000+3*(n+1)+(i+1)) = m (1000+3*(n+1)+(i+1)) :=
      Run_frame (SelAux n i) (fun d => 1000+4*(n+1) ≤ d) hge ⟨0, m⟩ (2*i) _ (by omega)
    have hfr3 : mi 3 = m 3 :=
      Run_frame (SelAux n i) (fun d => 1000+4*(n+1) ≤ d) hge ⟨0, m⟩ (2*i) 3 (by omega)
    have hAmp2 : ∀ t, ∀ pc ms,
        Run [Op.add (1000+4*(n+1)+(i+1)) (1000+2*(n+1)+(i+1)) (1000+3*(n+1)+(i+1)),
              Op.add (1000+4*(n+1)+(i+1)) (1000+4*(n+1)+(i+1)) 3] t ⟨0, mi⟩ = ⟨pc, ms⟩ →
          ∀ k, -1 ≤ ms k ∧ ms k ≤ Bnd r := by
      refine selblk_amp r (1000+4*(n+1)+(i+1)) (1000+2*(n+1)+(i+1)) (1000+3*(n+1)+(i+1)) hr mi
        (by rw [hfr3]; exact h3) (by omega) hmiB ?_ ?_
      · rw [hfrA, hfrB]; exact (hin (i+1) (by omega) hi).1
      · rw [hfrA, hfrB]; exact (hin (i+1) (by omega) hi).2
    have hEq : SelAux n (i+1) = (SelAux n i) ++ shiftProg (SelAux n i).length
        [Op.add (1000+4*(n+1)+(i+1)) (1000+2*(n+1)+(i+1)) (1000+3*(n+1)+(i+1)),
         Op.add (1000+4*(n+1)+(i+1)) (1000+4*(n+1)+(i+1)) 3] := rfl
    rw [hEq] at hrun
    exact Run_concat_amp (SelAux n i) _ (2*i) ⟨0, m⟩ mi r hpc1 h1 hAmp1 hAmp2 t pc ms hrun k

theorem Sel_amp (n r : ℕ) (hr : 1 ≤ r) (m : ℕ → ℤ) (h3 : m 3 = 1)
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r)
    (hin : ∀ j, 1 ≤ j → j ≤ n → -1 ≤ m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ∧
      m (1000+2*(n+1)+j) + m (1000+3*(n+1)+j) ≤ (2:ℤ)^(r-2) - 1) :
    ∀ t, ∀ pc ms, Run (Sel n) t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ k, -1 ≤ ms k ∧ ms k ≤ Bnd r :=
  SelAux_amp n r hr m h3 hm hin n le_rfl

/-! ## Arithmetic helpers for the amplitude bound -/

/-- The `O(n)` form of the amplitude bound of Theorem 1: `2^(2r) + 2000*(n+1)`. -/
def BndT (n r : ℕ) : ℤ := (2:ℤ)^(2*r) + 2000*((n:ℤ)+1)

theorem Bnd_le_BndT (n r : ℕ) : Bnd r ≤ BndT n r := by
  have : (0:ℤ) ≤ 2000*((n:ℤ)+1) := by positivity
  unfold Bnd BndT; linarith

theorem two_pow_le_two_pow2 (r : ℕ) (hr : 1 ≤ r) : (2:ℤ)^r ≤ (2:ℤ)^(2*r) :=
  pow_le_pow_right₀ (by norm_num) (by omega)

theorem r_le_Bnd (r : ℕ) (hr : 1 ≤ r) : (r:ℤ) ≤ Bnd r := by
  have h1 : (r:ℤ) ≤ (2:ℤ)^r := le_of_lt (by exact_mod_cast Nat.lt_two_pow_self (n := r))
  have h2 := two_pow_le_two_pow2 r hr
  unfold Bnd; linarith

theorem two_pow_le_Bnd (r : ℕ) (hr : 1 ≤ r) : (2:ℤ)^r ≤ Bnd r := by
  unfold Bnd; linarith [two_pow_le_two_pow2 r hr]

theorem prime_bound_le_Bnd (n r : ℕ) (hr : 1 ≤ r) (hpr : Nat.nth Nat.Prime n < 2^r) :
    (Nat.nth Nat.Prime n : ℤ) + 1001 ≤ Bnd r := by
  have h1 : (Nat.nth Nat.Prime n : ℤ) < (2:ℤ)^r := by exact_mod_cast hpr
  unfold Bnd; linarith [two_pow_le_two_pow2 r hr]

theorem n_succ_le_two_r (n r : ℕ) (hpr : Nat.nth Nat.Prime n < 2^r) : n + 1 < 2^r := by
  have h := Nat.add_two_le_nth_prime n
  omega

theorem two_n_add_le_Bnd (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hpr : Nat.nth Nat.Prime n < 2^r) :
    2*(n:ℤ) + 1001 ≤ Bnd r := by
  have hlt := n_succ_le_two_r n r hpr
  have h' : ((n:ℤ)+1) ≤ (2:ℤ)^r := by
    have hc : ((n+1 : ℕ) : ℤ) ≤ (2:ℤ)^r := by exact_mod_cast (le_of_lt hlt)
    push_cast at hc ⊢; linarith
  have hpoweq : (2:ℤ)^(r+1) = 2 * (2:ℤ)^r := by rw [pow_succ]; ring
  have h2 : (2:ℤ)^(r+1) ≤ (2:ℤ)^(2*r) := by
    apply pow_le_pow_right₀ (by norm_num); omega
  have hbig : 2*(n:ℤ) + 2 ≤ (2:ℤ)^(2*r) := by
    calc 2*(n:ℤ)+2 = 2*((n:ℤ)+1) := by ring
      _ ≤ 2 * (2:ℤ)^r := by linarith
      _ = (2:ℤ)^(r+1) := hpoweq.symm
      _ ≤ (2:ℤ)^(2*r) := h2
  unfold Bnd; linarith

theorem n_succ_le_Bnd (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hpr : Nat.nth Nat.Prime n < 2^r) :
    (n:ℤ) + 1 ≤ Bnd r := by
  have hlt := n_succ_le_two_r n r hpr
  have hc : ((n+1 : ℕ) : ℤ) ≤ (2:ℤ)^r := by exact_mod_cast (le_of_lt hlt)
  have h : ((n:ℤ)+1) ≤ (2:ℤ)^r := by push_cast at hc ⊢; linarith
  have h2 := two_pow_le_two_pow2 r hr
  unfold Bnd; linarith

theorem nth_prime_le_two_r (n r : ℕ) (hpr : Nat.nth Nat.Prime n < 2^r) :
    (Nat.nth Nat.Prime n : ℤ) ≤ (2:ℤ)^r := by
  exact_mod_cast (le_of_lt hpr)

/-! ## The prime phase -/

theorem run_stuck_from19 (n T : ℕ) (h : (run T (s0 n)).pc = 19) :
    ∀ s, run (T + s) (s0 n) = run T (s0 n) := by
  intro s
  induction s with
  | zero => rw [Nat.add_zero]
  | succ s ih =>
    rw [Nat.add_succ, run_succ, ih, state_pc_eq h, st19]

def Agree25 (m m' : ℕ → ℤ) : Prop := ∀ i, i ≠ 25 → m i = m' i

theorem update_agree25 {d a b : ℕ} (hd : d ≠ 25) (ha : a ≠ 25) (hb : b ≠ 25)
    {m m' : ℕ → ℤ} (h : Agree25 m m') :
    Agree25 (Function.update m d (m a + m b)) (Function.update m' d (m' a + m' b)) := by
  intro i hi
  by_cases hid : i = d
  · subst hid; rw [Function.update_self, Function.update_self, h a ha, h b hb]
  · rw [Function.update_of_ne hid, Function.update_of_ne hid]; exact h i hi

theorem update_agree25rem {d a b : ℕ} (hd : d ≠ 25) (ha : a ≠ 25) (hb : b ≠ 25)
    {m m' : ℕ → ℤ} (h : Agree25 m m') :
    Agree25 (Function.update m d (m a % m b)) (Function.update m' d (m' a % m' b)) := by
  intro i hi
  by_cases hid : i = d
  · subst hid; rw [Function.update_self, Function.update_self, h a ha, h b hb]
  · rw [Function.update_of_ne hid, Function.update_of_ne hid]; exact h i hi

theorem update_agree25_store (m m' : ℕ → ℤ) (h : Agree25 m m') (d : ℕ) (hd : d ≠ 25)
    (hv : m 11 = m' 11) : Agree25 (Function.update m d (m 11)) (Function.update m' d (m' 11)) := by
  intro i hi
  by_cases hid : i = d
  · subst hid; rw [Function.update_self, Function.update_self, hv]
  · rw [Function.update_of_ne hid, Function.update_of_ne hid]; exact h i hi

theorem prog_step_agree25 (pc : ℕ) (m m' : ℕ → ℤ) (h : Agree25 m m')
    (h15 : pc = 15 → (1000:ℤ) ≤ m 15) :
    (step ⟨pc, m⟩).pc = (step ⟨pc, m'⟩).pc ∧ Agree25 (step ⟨pc,m⟩).mem (step ⟨pc,m'⟩).mem := by
  have h10 := h 10 (by decide)
  have h11 := h 11 (by decide)
  have h12 := h 12 (by decide)
  have h13 := h 13 (by decide)
  have h14 := h 14 (by decide)
  have h15' := h 15 (by decide)
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  rcases Nat.lt_or_ge pc 20 with hp | hp
  · interval_cases pc
    · rw [st0]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st1]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · by_cases hh : m 10 = m 0
      · rw [st2eq m hh, st2eq m' (h10.symm.trans (hh.trans h0))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st2ne m hh, st2ne m' (by intro hc; exact hh (h10.trans hc |>.trans h0.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st3]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st4]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · by_cases hh : m 12 = m 11
      · rw [st5eq m hh, st5eq m' (h12.symm.trans (hh.trans h11))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st5ne m hh, st5ne m' (by intro hc; exact hh (h12.trans hc |>.trans h11.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st6]; exact ⟨rfl, update_agree25rem (by decide) (by decide) (by decide) h⟩
    · by_cases hh : m 14 = m 1
      · rw [st7eq m hh, st7eq m' (h14.symm.trans (hh.trans h1))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st7ne m hh, st7ne m' (by intro hc; exact hh (h14.trans hc |>.trans h1.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st8]; exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st9]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st10]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st11]; exact ⟨rfl, fun i hi => h i hi⟩
    · by_cases hh : m 13 = m 2
      · rw [st12eq m hh, st12eq m' (h13.symm.trans (hh.trans h2))]
        exact ⟨rfl, fun i hi => h i hi⟩
      · rw [st12ne m hh, st12ne m' (by intro hc; exact hh (h13.trans hc |>.trans h2.symm))]
        exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st13]; exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st14]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st15 m, st15 m']
      refine ⟨rfl, ?_⟩
      intro i hi
      have hge : (1000:ℤ) ≤ m 15 := h15 rfl
      have hdn : (m 15).toNat = (m' 15).toNat := by rw [h15']
      have hd25 : (m 15).toNat ≠ 25 := by
        intro hc
        have hnn : (0:ℤ) ≤ m 15 := by omega
        have h1' := Int.toNat_of_nonneg hnn
        rw [hc] at h1'
        omega
      have hv : m 11 = m' 11 := h11
      rw [hdn]
      exact update_agree25_store m m' h (m' 15).toNat (hdn ▸ hd25) hv i hi
    · rw [st16]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st17]; exact ⟨rfl, update_agree25 (by decide) (by decide) (by decide) h⟩
    · rw [st18]; exact ⟨rfl, fun i hi => h i hi⟩
    · rw [st19]; exact ⟨rfl, fun i hi => h i hi⟩
  · have hnone : prog[pc]? = none := by rw [List.getElem?_eq_none_iff]; simp [prog]; omega
    rw [show step ⟨pc,m⟩ = ⟨pc,m⟩ from by simp only [step, hnone],
      show step ⟨pc,m'⟩ = ⟨pc,m'⟩ from by simp only [step, hnone]]
    exact ⟨rfl, fun i hi => h i hi⟩

theorem run_agree25 (n r : ℕ) :
    ∀ t, (run t ⟨0, initMem (n+1)⟩).pc = (run t ⟨0, m0 n r⟩).pc ∧
         FrameInv (run t ⟨0, initMem (n+1)⟩).pc (run t ⟨0, initMem (n+1)⟩).mem ∧
         Agree25 (run t ⟨0, initMem (n+1)⟩).mem (run t ⟨0, m0 n r⟩).mem := by
  intro t
  induction t with
  | zero =>
    have hfr : FrameInv 0 (initMem (n+1)) :=
      ⟨by simp [initMem], by simp [initMem], by simp [initMem, BASE], by simp [initMem],
       by omega⟩
    refine ⟨rfl, hfr, ?_⟩
    intro i hi
    show (initMem (n+1)) i = (Function.update (initMem (n+1)) 25 (r:ℤ)) i
    rw [Function.update_of_ne hi]
  | succ t ih =>
    obtain ⟨ihpc, ihfr, ihag⟩ := ih
    set p := (run t ⟨0, initMem (n+1)⟩).pc with hp
    set M := (run t ⟨0, initMem (n+1)⟩).mem with hM
    set M' := (run t ⟨0, m0 n r⟩).mem with hM'
    have hst : run t ⟨0, initMem (n+1)⟩ = ⟨p, M⟩ := state_pc_eq rfl
    have hst' : run t ⟨0, m0 n r⟩ = ⟨p, M'⟩ := state_pc_eq ihpc.symm
    have hfr2 := prog_frame_step p M (by rw [hp, hM]; exact ihfr)
    have hag2 := prog_step_agree25 p M M' (by rw [hM, hM']; exact ihag)
      (by rw [hp, hM]; exact ihfr.2.2.2.2)
    rw [run_succ, run_succ, hst, hst']
    exact ⟨hag2.1, hfr2.1, hag2.2⟩

def PNonneg (mem : ℕ → ℤ) : Prop := ∀ i, 0 ≤ mem i

theorem rem_nonneg {a b : ℤ} (ha : 0 ≤ a) : 0 ≤ a % b := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; rw [Int.emod_zero]; exact ha
  · exact Int.emod_nonneg a hb

theorem upd_nonneg {d a b : ℕ} {m : ℕ → ℤ} (h : PNonneg m) :
    PNonneg (Function.update m d (m a + m b)) := by
  intro i
  by_cases hid : i = d
  · subst hid; rw [Function.update_self]; exact add_nonneg (h a) (h b)
  · rw [Function.update_of_ne hid]; exact h i

theorem upd_rem_nonneg {d a b : ℕ} {m : ℕ → ℤ} (h : PNonneg m) :
    PNonneg (Function.update m d (m a % m b)) := by
  intro i
  by_cases hid : i = d
  · subst hid; rw [Function.update_self]; exact rem_nonneg (h a)
  · rw [Function.update_of_ne hid]; exact h i

theorem upd_nonnegv {d : ℕ} {v : ℤ} {m : ℕ → ℤ} (h : PNonneg m) (hv : 0 ≤ v) :
    PNonneg (Function.update m d v) := by
  intro i
  by_cases hid : i = d
  · subst hid; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hid]; exact h i

theorem prog_step_nonneg (pc : ℕ) (m : ℕ → ℤ) (h : PNonneg m) : PNonneg (step ⟨pc, m⟩).mem := by
  rcases Nat.lt_or_ge pc 20 with hp | hp
  · interval_cases pc
    · rw [st0]; exact upd_nonneg h
    · rw [st1]; exact upd_nonneg h
    · by_cases hh : m 10 = m 0
      · rw [st2eq m hh]; exact h
      · rw [st2ne m hh]; exact h
    · rw [st3]; exact upd_nonneg h
    · rw [st4]; exact upd_nonneg h
    · by_cases hh : m 12 = m 11
      · rw [st5eq m hh]; exact h
      · rw [st5ne m hh]; exact h
    · rw [st6]; exact upd_rem_nonneg h
    · by_cases hh : m 14 = m 1
      · rw [st7eq m hh]; exact h
      · rw [st7ne m hh]; exact h
    · rw [st8]; exact h
    · rw [st9]; exact upd_nonneg h
    · rw [st10]; exact upd_nonneg h
    · rw [st11]; exact h
    · by_cases hh : m 13 = m 2
      · rw [st12eq m hh]; exact h
      · rw [st12ne m hh]; exact h
    · rw [st13]; exact h
    · rw [st14]; exact upd_nonneg h
    · rw [st15]; exact upd_nonnegv h (h 11)
    · rw [st16]; exact upd_nonneg h
    · rw [st17]; exact upd_nonneg h
    · rw [st18]; exact h
    · rw [st19]; exact h
  · have hnone : prog[pc]? = none := by rw [List.getElem?_eq_none_iff]; simp [prog]; omega
    rw [show step ⟨pc,m⟩ = ⟨pc,m⟩ from by simp only [step, hnone]]
    exact h

theorem run_nonneg (n r : ℕ) : ∀ t, PNonneg (run t ⟨0, m0 n r⟩).mem := by
  intro t
  induction t with
  | zero =>
    intro i
    by_cases hi : i = 25
    · subst hi
      show (0:ℤ) ≤ (Function.update (initMem (n+1)) 25 (r:ℤ)) 25
      rw [Function.update_self]; omega
    · show (0:ℤ) ≤ (Function.update (initMem (n+1)) 25 (r:ℤ)) i
      rw [Function.update_of_ne hi]
      simp only [initMem]
      split_ifs <;> omega
  | succ t ih =>
    rw [run_succ]
    exact prog_step_nonneg _ _ ih

theorem prime_amp (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hpr : Nat.nth Nat.Prime n < 2^r) :
    ∀ t, ∀ pc ms, Run (prog.take 19) t ⟨0, m0 n r⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hpbound : (Nat.nth Nat.Prime n : ℤ) + 1001 ≤ Bnd r := prime_bound_le_Bnd n r hr hpr
  have hrB : (r:ℤ) ≤ Bnd r := r_le_Bnd r hr
  obtain ⟨T, hT, mem, hrun, hout, hamp⟩ := main_bounded_all (n+1)
  have hampn : ∀ t ≤ T, ∀ pc ms, run t (s0 (n+1)) = ⟨pc, ms⟩ →
      ∀ i, ms i ≤ (Nat.nth Nat.Prime n : ℤ) + 1001 := by
    intro t ht pc ms h' i
    have h2 := hamp t ht pc ms h' i
    rwa [show (n+1) - 1 = n from Nat.add_sub_cancel n 1] at h2
  have hpcr : (run T (s0 (n+1))).pc = 19 := congrArg State.pc hrun
  have hs0amp : ∀ t, ∀ pc ms, run t (s0 (n+1)) = ⟨pc, ms⟩ → ∀ i, ms i ≤ Bnd r := by
    intro t
    rcases lt_or_ge t T with ht | ht
    · intro pc ms h' i
      exact le_trans (hampn t (le_of_lt ht) pc ms h' i) hpbound
    · intro pc ms h' i
      have hst : run t (s0 (n+1)) = ⟨19, mem⟩ := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
        rw [run_stuck_from19 (n+1) T hpcr s, hrun]
      have hms : ms = mem := congrArg State.mem (h'.symm.trans hst)
      rw [hms]; exact le_trans (hampn T le_rfl 19 mem hrun i) hpbound
  have hampM0 : ∀ t, ∀ pc ms, run t ⟨0, m0 n r⟩ = ⟨pc, ms⟩ → ∀ i, ms i ≤ Bnd r := by
    intro t pc ms h' i
    have hmem : ∀ k, (run t ⟨0, m0 n r⟩).mem k = ms k :=
      fun k => congrArg (fun f => f k) (congrArg State.mem h')
    by_cases hi25 : i = 25
    · subst hi25
      have hfr0 : FrameInv 0 (m0 n r) := by
        refine ⟨?_, ?_, ?_, ?_, by omega⟩
        · show (Function.update (initMem (n+1)) 25 (r:ℤ)) 1 = 0
          rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 25)]; simp [initMem]
        · show (Function.update (initMem (n+1)) 25 (r:ℤ)) 2 = 1
          rw [Function.update_of_ne (by decide : (2:ℕ) ≠ 25)]; simp [initMem]
        · show (Function.update (initMem (n+1)) 25 (r:ℤ)) 4 = 1000
          rw [Function.update_of_ne (by decide : (4:ℕ) ≠ 25)]; simp [initMem, BASE]
        · show (0:ℤ) ≤ (Function.update (initMem (n+1)) 25 (r:ℤ)) 10
          rw [Function.update_of_ne (by decide : (10:ℕ) ≠ 25)]; simp [initMem]
      obtain ⟨_, hframe⟩ := prog_run_frame (m0 n r) 0 hfr0 t
      have h25 : ms 25 = (r:ℤ) := by
        rw [← hmem 25, hframe 25 (by omega) (by omega)]
        show (Function.update (initMem (n+1)) 25 (r:ℤ)) 25 = (r:ℤ)
        rw [Function.update_self]
      rw [h25]; exact hrB
    · have hag := (run_agree25 n r t).2.2 i hi25
      rw [← hmem i, ← hag]
      exact hs0amp t _ _ rfl i
  have hM0nn : ∀ t, ∀ pc ms, run t ⟨0, m0 n r⟩ = ⟨pc, ms⟩ → ∀ i, 0 ≤ ms i := by
    intro t pc ms h' i
    have hmem : ∀ k, (run t ⟨0, m0 n r⟩).mem k = ms k :=
      fun k => congrArg (fun f => f k) (congrArg State.mem h')
    rw [← hmem i]
    exact run_nonneg n r t i
  have hpcm0 : (run T ⟨0, m0 n r⟩).pc = 19 := ((run_agree25 n r T).1).symm.trans hpcr
  obtain ⟨Tstar, hTle, hlt, hstar⟩ := first_hit (P := prog) (s := ⟨0, m0 n r⟩) (T1 := T)
    (L := 19) (m1 := (run T ⟨0, m0 n r⟩).mem) (fun m => st19 m) (by decide)
    (by rw [Run_prog]; exact state_pc_eq hpcm0)
  have hagree : ∀ k, k < 19 → (prog.take 19)[k]? = prog[k]? :=
    fun k hk => List.getElem?_take_of_lt hk
  have hpref : ∀ t ≤ Tstar, Run (prog.take 19) t ⟨0, m0 n r⟩ = run t ⟨0, m0 n r⟩ :=
    fun t ht => (Run_prefix_eq prog (prog.take 19) 19 Tstar ⟨0, m0 n r⟩ hagree hlt t ht).trans
      (Run_prog t _)
  have hstar' : Run (prog.take 19) Tstar ⟨0, m0 n r⟩ = ⟨19, (run T ⟨0, m0 n r⟩).mem⟩ :=
    (hpref Tstar le_rfl).trans ((Run_prog Tstar ⟨0, m0 n r⟩).symm.trans hstar)
  have hnone : (prog.take 19)[19]? = none := by
    rw [List.getElem?_eq_none_iff]; simp [take19_len]
  intro t pc ms hrun' i
  rcases lt_or_ge t Tstar with ht | ht
  · rw [hpref t (le_of_lt ht)] at hrun'
    exact ⟨by have := hM0nn t _ _ hrun' i; omega, hampM0 t _ _ hrun' i⟩
  · have hstuck : Run (prog.take 19) t ⟨0, m0 n r⟩ = Run (prog.take 19) Tstar ⟨0, m0 n r⟩ := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      rw [Run_add, hstar']
      exact Run_stuck_none (prog.take 19) ⟨19, (run T ⟨0, m0 n r⟩).mem⟩ hnone s
    rw [hstuck, hstar'] at hrun'
    have hms : ms = (run Tstar ⟨0, m0 n r⟩).mem := by
      have h1 : ms = (run T ⟨0, m0 n r⟩).mem := congrArg State.mem hrun'.symm
      have hstar'' : run Tstar ⟨0, m0 n r⟩ = (⟨19, (run T ⟨0, m0 n r⟩).mem⟩ : State) :=
        (hpref Tstar le_rfl).symm.trans hstar'
      have h2 : (run Tstar ⟨0, m0 n r⟩).mem = (run T ⟨0, m0 n r⟩).mem :=
        (by rw [hstar''])
      rw [h1, ← h2]
    refine ⟨?_, ?_⟩
    · rw [hms]; exact le_trans (by norm_num : (-1:ℤ) ≤ 0) (hM0nn Tstar _ _ (state_pc_eq rfl) i)
    · rw [hms]; exact hampM0 Tstar _ _ (state_pc_eq rfl) i



/-! ## The setup program: amplitude of the constant-register phase -/

/-- Register written by the `k`-th instruction of `Sconst`. -/
def scReg : ℕ → ℕ
  | 0 => 31 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 11
  | 8 => 12 | 9 => 23 | 10 => 35 | 11 => 26 | 12 => 27 | _ => 27

/-- Value written by the `k`-th instruction of `Sconst`. -/
def scVal (n : ℕ) : ℕ → ℤ
  | 0 => 1000 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 0
  | 8 => 0 | 9 => 0 | 10 => (n:ℤ) | 11 => 1 | 12 => 0 | _ => 0

@[simp] theorem scReg_0 : scReg 0 = 31 := rfl
@[simp] theorem scReg_1 : scReg 1 = 4 := rfl
@[simp] theorem scReg_2 : scReg 2 = 3 := rfl
@[simp] theorem scReg_3 : scReg 3 = 2 := rfl
@[simp] theorem scReg_4 : scReg 4 = 5 := rfl
@[simp] theorem scReg_5 : scReg 5 = 6 := rfl
@[simp] theorem scReg_6 : scReg 6 = 7 := rfl
@[simp] theorem scReg_7 : scReg 7 = 11 := rfl
@[simp] theorem scReg_8 : scReg 8 = 12 := rfl
@[simp] theorem scReg_9 : scReg 9 = 23 := rfl
@[simp] theorem scReg_10 : scReg 10 = 35 := rfl
@[simp] theorem scReg_11 : scReg 11 = 26 := rfl
@[simp] theorem scReg_12 : scReg 12 = 27 := rfl
@[simp] theorem scVal_0 (n : ℕ) : scVal n 0 = 1000 := rfl
@[simp] theorem scVal_1 (n : ℕ) : scVal n 1 = 2 := rfl
@[simp] theorem scVal_2 (n : ℕ) : scVal n 2 = 1 := rfl
@[simp] theorem scVal_3 (n : ℕ) : scVal n 3 = 0 := rfl
@[simp] theorem scVal_4 (n : ℕ) : scVal n 4 = 3 := rfl
@[simp] theorem scVal_5 (n : ℕ) : scVal n 5 = 4 := rfl
@[simp] theorem scVal_6 (n : ℕ) : scVal n 6 = 5 := rfl
@[simp] theorem scVal_7 (n : ℕ) : scVal n 7 = 0 := rfl
@[simp] theorem scVal_8 (n : ℕ) : scVal n 8 = 0 := rfl
@[simp] theorem scVal_9 (n : ℕ) : scVal n 9 = 0 := rfl
@[simp] theorem scVal_10 (n : ℕ) : scVal n 10 = (n:ℤ) := rfl
@[simp] theorem scVal_11 (n : ℕ) : scVal n 11 = 1 := rfl
@[simp] theorem scVal_12 (n : ℕ) : scVal n 12 = 0 := rfl

theorem scReg_inj : ∀ j, j < 13 → ∀ k, k < 13 → scReg j = scReg k → j = k := by
  intro j hj k hk h
  interval_cases j <;> interval_cases k <;> simp_all [scReg]

theorem scReg_ne_of_ne : ∀ k, k < 13 → ∀ j, j < 13 → k ≠ j → scReg k ≠ scReg j :=
  fun k hk j hj hne h => hne (scReg_inj k hk j hj h)

theorem scReg_ne0 : ∀ j, j < 13 → scReg j ≠ 0 := by
  intro j hj; interval_cases j <;> decide
theorem scReg_ne1 : ∀ j, j < 13 → scReg j ≠ 1 := by
  intro j hj; interval_cases j <;> decide

theorem Sconst_length : Sconst.length = 13 := rfl

theorem Sc0m (m : ℕ → ℤ) :
    (stepP Sconst ⟨0, m⟩).mem = Function.update m (scReg 0) (m (scReg 1) + m 1) := rfl
theorem Sc1m (m : ℕ → ℤ) :
    (stepP Sconst ⟨1, m⟩).mem = Function.update m (scReg 1) (m (scReg 3) + m (scReg 3)) := rfl
theorem Sc2m (m : ℕ → ℤ) :
    (stepP Sconst ⟨2, m⟩).mem = Function.update m (scReg 2) (m (scReg 3) + m 1) := rfl
theorem Sc3m (m : ℕ → ℤ) :
    (stepP Sconst ⟨3, m⟩).mem = Function.update m (scReg 3) (m 1 - m 1) := rfl
theorem Sc4m (m : ℕ → ℤ) :
    (stepP Sconst ⟨4, m⟩).mem = Function.update m (scReg 4) (m (scReg 1) + m (scReg 2)) := rfl
theorem Sc5m (m : ℕ → ℤ) :
    (stepP Sconst ⟨5, m⟩).mem = Function.update m (scReg 5) (m (scReg 1) + m (scReg 1)) := rfl
theorem Sc6m (m : ℕ → ℤ) :
    (stepP Sconst ⟨6, m⟩).mem = Function.update m (scReg 6) (m (scReg 4) + m (scReg 1)) := rfl
theorem Sc7m (m : ℕ → ℤ) :
    (stepP Sconst ⟨7, m⟩).mem = Function.update m (scReg 7) (m 1 - m 1) := rfl
theorem Sc8m (m : ℕ → ℤ) :
    (stepP Sconst ⟨8, m⟩).mem = Function.update m (scReg 8) (m 1 - m 1) := rfl
theorem Sc9m (m : ℕ → ℤ) :
    (stepP Sconst ⟨9, m⟩).mem = Function.update m (scReg 9) (m 1 - m 1) := rfl
theorem Sc10m (m : ℕ → ℤ) :
    (stepP Sconst ⟨10, m⟩).mem = Function.update m (scReg 10) (m 0 - m (scReg 2)) := rfl
theorem Sc11m (m : ℕ → ℤ) :
    (stepP Sconst ⟨11, m⟩).mem = Function.update m (scReg 11) (m (scReg 2) + m 1) := rfl
theorem Sc12m (m : ℕ → ℤ) :
    (stepP Sconst ⟨12, m⟩).mem = Function.update m (scReg 12) (m 1 - m 1) := rfl

theorem const_le_Bnd (r : ℕ) (c : ℕ) (hc : c ≤ 2000) : (c:ℤ) ≤ Bnd r := by
  unfold Bnd; linarith [pow_nonneg (by norm_num : (0:ℤ) ≤ 2) (2*r)]

/-- Invariant of `Sconst`: the memory agrees with `scVal` on the registers written so far,
and with the incoming memory elsewhere (`0`, `1` are never written). -/
def ScGood (n : ℕ) (m mm : ℕ → ℤ) (t : ℕ) : Prop :=
  mm 0 = m 0 ∧ mm 1 = m 1 ∧
  (∀ k, k < t → k < 13 → mm (scReg k) = scVal n k) ∧
  (∀ i, (∀ k, k < t → k < 13 → scReg k ≠ i) → mm i = m i)

theorem ScGood_zero {n : ℕ} {m mm : ℕ → ℤ} {t : ℕ} (h : ScGood n m mm t) : mm 0 = m 0 := h.1
theorem ScGood_one {n : ℕ} {m mm : ℕ → ℤ} {t : ℕ} (h : ScGood n m mm t) : mm 1 = m 1 := h.2.1
theorem ScGood_w {n : ℕ} {m mm : ℕ → ℤ} {t : ℕ} (h : ScGood n m mm t) {k : ℕ}
    (hk : k < t) (hk13 : k < 13) : mm (scReg k) = scVal n k := h.2.2.1 k hk hk13
theorem ScGood_u {n : ℕ} {m mm : ℕ → ℤ} {t : ℕ} (h : ScGood n m mm t) {i : ℕ}
    (hi : ∀ k, k < t → k < 13 → scReg k ≠ i) : mm i = m i := h.2.2.2 i hi
theorem ScGood_g {n : ℕ} {m mm : ℕ → ℤ} {t : ℕ} (h : ScGood n m mm t) {k : ℕ}
    (hk : t ≤ k) (hk13 : k < 13) : mm (scReg k) = m (scReg k) :=
  ScGood_u h (fun j hj hj13 => scReg_ne_of_ne j hj13 k hk13 (by omega))

theorem ScGood_init (n : ℕ) (m : ℕ → ℤ) : ScGood n m m 0 :=
  ⟨rfl, rfl, by intro k hk; omega, by intro i _; rfl⟩

theorem ScGood_step (n : ℕ) (m mm : ℕ → ℤ) (t : ℕ) (ht : t < 13)
    (hgood : ScGood n m mm t)
    (h0 : m 0 = (n:ℤ)+1) (h1 : m 1 = 0) (h2 : m 2 = 1) (h3 : m 3 = 2) (h4 : m 4 = 1000) :
    ScGood n m (stepP Sconst ⟨t, mm⟩).mem (t+1) := by
  obtain ⟨v, hv, hvval⟩ :
      ∃ v, (stepP Sconst ⟨t, mm⟩).mem = Function.update mm (scReg t) v ∧ v = scVal n t := by
    interval_cases t
    · exact ⟨mm (scReg 1) + mm 1, rfl, by
        have hg : mm (scReg 1) = m (scReg 1) := ScGood_g hgood (by omega) (by decide)
        rw [scReg_1] at hg ⊢
        rw [scVal_0, hg, ScGood_one hgood, h4, h1]; norm_num⟩
    · exact ⟨mm (scReg 3) + mm (scReg 3), rfl, by
        have hg : mm (scReg 3) = m (scReg 3) := ScGood_g hgood (by omega) (by decide)
        rw [scReg_3] at hg ⊢
        rw [scVal_1, hg, h2]; norm_num⟩
    · exact ⟨mm (scReg 3) + mm 1, rfl, by
        have hg : mm (scReg 3) = m (scReg 3) := ScGood_g hgood (by omega) (by decide)
        rw [scReg_3] at hg ⊢
        rw [scVal_2, hg, ScGood_one hgood, h2, h1]; norm_num⟩
    · exact ⟨mm 1 - mm 1, rfl, by
        rw [scVal_3, ScGood_one hgood, h1]; norm_num⟩
    · exact ⟨mm (scReg 1) + mm (scReg 2), rfl, by
        have hg1 : mm (scReg 1) = scVal n 1 := ScGood_w hgood (by omega) (by decide)
        have hg2 : mm (scReg 2) = scVal n 2 := ScGood_w hgood (by omega) (by decide)
        rw [scVal_4, hg1, hg2, scVal_1, scVal_2]; norm_num⟩
    · exact ⟨mm (scReg 1) + mm (scReg 1), rfl, by
        have hg1 : mm (scReg 1) = scVal n 1 := ScGood_w hgood (by omega) (by decide)
        rw [scVal_5, hg1, scVal_1]; norm_num⟩
    · exact ⟨mm (scReg 4) + mm (scReg 1), rfl, by
        have hg1 : mm (scReg 4) = scVal n 4 := ScGood_w hgood (by omega) (by decide)
        have hg2 : mm (scReg 1) = scVal n 1 := ScGood_w hgood (by omega) (by decide)
        rw [scVal_6, hg1, hg2, scVal_4, scVal_1]; norm_num⟩
    · exact ⟨mm 1 - mm 1, rfl, by
        rw [scVal_7, ScGood_one hgood, h1]; norm_num⟩
    · exact ⟨mm 1 - mm 1, rfl, by
        rw [scVal_8, ScGood_one hgood, h1]; norm_num⟩
    · exact ⟨mm 1 - mm 1, rfl, by
        rw [scVal_9, ScGood_one hgood, h1]; norm_num⟩
    · exact ⟨mm 0 - mm (scReg 2), rfl, by
        have hg : mm (scReg 2) = scVal n 2 := ScGood_w hgood (by omega) (by decide)
        rw [scVal_10, ScGood_zero hgood, hg, scVal_2, h0]; ring⟩
    · exact ⟨mm (scReg 2) + mm 1, rfl, by
        have hg : mm (scReg 2) = scVal n 2 := ScGood_w hgood (by omega) (by decide)
        rw [scVal_11, hg, scVal_2, ScGood_one hgood, h1]; norm_num⟩
    · exact ⟨mm 1 - mm 1, rfl, by
        rw [scVal_12, ScGood_one hgood, h1]; norm_num⟩
  rw [hv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (scReg_ne0 t (by omega)).symm]; exact ScGood_zero hgood
  · rw [Function.update_of_ne (scReg_ne1 t (by omega)).symm]; exact ScGood_one hgood
  · intro k hk hk13
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkl | hke
    · rw [Function.update_of_ne (scReg_ne_of_ne k hk13 t (by omega) (by omega))]
      exact ScGood_w hgood hkl hk13
    · subst hke; rw [Function.update_self]; exact hvval
  · intro i hi
    rw [Function.update_of_ne (hi t (by omega) (by omega)).symm]
    exact ScGood_u hgood (fun k hk hk13 => hi k (by omega) hk13)

theorem amp_of_ScGood (n r : ℕ) (m mm : ℕ → ℤ) (t : ℕ)
    (hgood : ScGood n m mm t) (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r)
    (hn : (n:ℤ) ≤ Bnd r) (hB1000 : (1000:ℤ) ≤ Bnd r) :
    ∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r := by
  intro i
  by_cases hw : ∃ k, k < t ∧ k < 13 ∧ scReg k = i
  · obtain ⟨k, hk, hk13, rfl⟩ := hw
    rw [ScGood_w hgood hk hk13]
    interval_cases k <;> simp only [scVal_0, scVal_1, scVal_2, scVal_3, scVal_4, scVal_5,
      scVal_6, scVal_7, scVal_8, scVal_9, scVal_10, scVal_11, scVal_12] <;> omega
  · rw [ScGood_u hgood (fun k hk hk13 hc => hw ⟨k, hk, hk13, hc⟩)]
    exact hm i

theorem Sconst_amp (n r : ℕ) (m : ℕ → ℤ)
    (h0 : m 0 = (n:ℤ)+1) (h1 : m 1 = 0) (h2 : m 2 = 1) (h3 : m 3 = 2) (h4 : m 4 = 1000)
    (hn : (n:ℤ) ≤ Bnd r) (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run Sconst t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hB1000 : (1000:ℤ) ≤ Bnd r := const_le_Bnd r 1000 (by norm_num)
  have hgood : ∀ t ≤ 13, ScGood n m (Run Sconst t ⟨0, m⟩).mem t := by
    intro t ht
    induction t with
    | zero => exact ScGood_init n m
    | succ t ih =>
      have hlt : t < 13 := by omega
      have hst : Run Sconst t ⟨0, m⟩ = ⟨t, (Run Sconst t ⟨0, m⟩).mem⟩ :=
        state_pc_eq (Sconst_pc m t (by omega))
      have hstep := ScGood_step n m (Run Sconst t ⟨0, m⟩).mem t hlt (ih (by omega)) h0 h1 h2 h3 h4
      rw [Run_succ, hst]
      exact hstep
  intro t pc ms hrun i
  by_cases ht : t ≤ 13
  · have hpct : (Run Sconst t ⟨0, m⟩).pc = t := Sconst_pc m t ht
    have hms : ms = (Run Sconst t ⟨0, m⟩).mem :=
      congrArg State.mem (hrun.symm.trans (state_pc_eq hpct))
    rw [hms]
    exact amp_of_ScGood n r m _ t (hgood t ht) hm hn hB1000 i
  · have hnone : Sconst[13]? = none := rfl
    have hst : Run Sconst t ⟨0, m⟩ = Run Sconst 13 ⟨0, m⟩ := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp ht))
      rw [Run_add]
      exact Run_stuck_none Sconst (Run Sconst 13 ⟨0, m⟩) hnone s
    have hpc13 : (Run Sconst 13 ⟨0, m⟩).pc = 13 := Sconst_pc m 13 le_rfl
    have hms : ms = (Run Sconst 13 ⟨0, m⟩).mem :=
      congrArg State.mem (hrun.symm.trans (hst.trans (state_pc_eq hpc13)))
    rw [hms]
    exact amp_of_ScGood n r m _ 13 (hgood 13 le_rfl) hm hn hB1000 i

/-! ## The setup program: amplitude of the doubling loop -/

theorem amp_update26 {r : ℕ} {mm : ℕ → ℤ} (h : ∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r) {v : ℤ}
    (hv : -1 ≤ v ∧ v ≤ Bnd r) :
    ∀ i, -1 ≤ (Function.update mm 26 v) i ∧ (Function.update mm 26 v) i ≤ Bnd r := by
  intro i
  rcases eq_or_ne i 26 with rfl | hi
  · rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hi]; exact h i

theorem amp_update27 {r : ℕ} {mm : ℕ → ℤ} (h : ∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r) {v : ℤ}
    (hv : -1 ≤ v ∧ v ≤ Bnd r) :
    ∀ i, -1 ≤ (Function.update mm 27 v) i ∧ (Function.update mm 27 v) i ≤ Bnd r := by
  intro i
  rcases eq_or_ne i 27 with rfl | hi
  · rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hi]; exact h i

theorem two_pow_le_Bnd' (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) : (2:ℤ)^k ≤ Bnd r :=
  le_trans (pow_le_pow_right₀ (by norm_num) hk) (two_pow_le_Bnd r hr)

theorem nat_le_Bnd (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) : (k:ℤ) ≤ Bnd r :=
  le_trans (by exact_mod_cast hk) (r_le_Bnd r hr)

theorem nat_succ_le_Bnd (r k : ℕ) (hr : 1 ≤ r) (hk : k < r) : ((k:ℤ)+1) ≤ Bnd r := by
  have h1 : ((k+1 : ℕ) : ℤ) ≤ Bnd r := nat_le_Bnd r (k+1) hr (by omega)
  push_cast at h1; linarith

/-- One-step invariant of the doubling loop. -/
def SdInv (r : ℕ) (pc : ℕ) (mm : ℕ → ℤ) : Prop :=
  (∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r) ∧ mm 25 = (r:ℤ) ∧ mm 3 = 1 ∧
  ((pc = 0 → ∃ k ≤ r, mm 27 = (k:ℤ) ∧ mm 26 = (2:ℤ)^k) ∧
   (pc = 1 → ∃ k < r, mm 27 = (k:ℤ) ∧ mm 26 = (2:ℤ)^k) ∧
   (pc = 2 → ∃ k < r, mm 27 = (k:ℤ) ∧ mm 26 = (2:ℤ)^(k+1)) ∧
   (pc = 3 → ∃ k < r, mm 27 = ((k:ℤ)+1) ∧ mm 26 = (2:ℤ)^(k+1)) ∧
   (pc = 4 → ∃ k ≤ r, mm 27 = (k:ℤ) ∧ mm 26 = (2:ℤ)^k))

theorem SdInv_amp {r pc : ℕ} {mm : ℕ → ℤ} (h : SdInv r pc mm) :
    ∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r := h.1

theorem SdInv_init (r : ℕ) (m : ℕ → ℤ) (h27 : m 27 = 0) (h26 : m 26 = 1)
    (h25 : m 25 = (r:ℤ)) (h3 : m 3 = 1) (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    SdInv r 0 m := by
  refine ⟨hm, h25, h3, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc
  · exact ⟨0, Nat.zero_le r, by rw [h27]; norm_num, by rw [h26]; norm_num⟩
  · omega
  · omega
  · omega
  · omega

theorem SdInv_step (r : ℕ) (hr : 1 ≤ r) (pc : ℕ) (mm : ℕ → ℤ) (h : SdInv r pc mm) :
    SdInv r (stepP Sdouble ⟨pc, mm⟩).pc (stepP Sdouble ⟨pc, mm⟩).mem := by
  obtain ⟨hamp, h25, h3, h0, h1, h2, h3c, h4⟩ := h
  rcases lt_or_ge pc 4 with hp | hp
  · interval_cases pc
    · obtain ⟨k, hkr, h27k, h26k⟩ := h0 rfl
      rcases eq_or_ne k r with hkeq | hkne
      · rw [Sd0 mm (by rw [h27k, h25, hkeq])]
        show SdInv r 4 mm
        exact ⟨hamp, h25, h3, (by intro hc; omega), (by intro hc; omega), (by intro hc; omega),
          (by intro hc; omega), fun _ => ⟨k, hkr, h27k, h26k⟩⟩
      · rw [Sd0' mm (by rw [h27k, h25]; exact fun hc => hkne (by exact_mod_cast hc))]
        show SdInv r 1 mm
        exact ⟨hamp, h25, h3, (by intro hc; omega), (fun _ => ⟨k, by omega, h27k, h26k⟩),
          (by intro hc; omega), (by intro hc; omega), (by intro hc; omega)⟩
    · obtain ⟨k, hkr, h27k, h26k⟩ := h1 rfl
      have hval : Sd1m mm = Function.update mm 26 ((2:ℤ)^(k+1)) := by
        unfold Sd1m; rw [h26k]; congr 1; rw [pow_succ]; ring
      have hv : -1 ≤ (2:ℤ)^(k+1) ∧ (2:ℤ)^(k+1) ≤ Bnd r :=
        ⟨by have hpos : (0:ℤ) ≤ (2:ℤ)^(k+1) := pow_nonneg (by norm_num) _; omega,
         two_pow_le_Bnd' r (k+1) hr (by omega)⟩
      rw [Sd1 mm, hval]
      show SdInv r 2 (Function.update mm 26 ((2:ℤ)^(k+1)))
      refine ⟨amp_update26 hamp hv, ?_, ?_, (by intro hc; omega), (by intro hc; omega),
        (fun _ => ⟨k, hkr, ?_, rfl⟩), (by intro hc; omega), (by intro hc; omega)⟩
      · rw [Function.update_of_ne (by decide : (25:ℕ) ≠ 26)]; exact h25
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 26)]; exact h3
      · rw [Function.update_of_ne (by decide : (27:ℕ) ≠ 26)]; exact h27k
    · obtain ⟨k, hkr, h27k, h26k⟩ := h2 rfl
      have hval : Sd2m mm = Function.update mm 27 ((k:ℤ)+1) := by
        unfold Sd2m; rw [h27k, h3]
      have hv : -1 ≤ (k:ℤ)+1 ∧ (k:ℤ)+1 ≤ Bnd r :=
        ⟨by omega, nat_succ_le_Bnd r k hr hkr⟩
      rw [Sd2 mm, hval]
      show SdInv r 3 (Function.update mm 27 ((k:ℤ)+1))
      refine ⟨amp_update27 hamp hv, ?_, ?_, (by intro hc; omega), (by intro hc; omega),
        (by intro hc; omega), (fun _ => ⟨k, hkr, ?_, ?_⟩), (by intro hc; omega)⟩
      · rw [Function.update_of_ne (by decide : (25:ℕ) ≠ 27)]; exact h25
      · rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 27)]; exact h3
      · rw [Function.update_self]
      · rw [Function.update_of_ne (by decide : (26:ℕ) ≠ 27)]; exact h26k
    · obtain ⟨k, hkr, h27k, h26k⟩ := h3c rfl
      rw [Sd3 mm]
      show SdInv r 0 mm
      exact ⟨hamp, h25, h3,
        (fun _ => ⟨k+1, by omega, by rw [h27k]; push_cast; ring, by rw [h26k]⟩),
        (by intro hc; omega), (by intro hc; omega), (by intro hc; omega), (by intro hc; omega)⟩
  · by_cases hpe : pc = 4
    · subst hpe
      rw [Sdl mm]
      show SdInv r 4 mm
      exact ⟨hamp, h25, h3, (by intro hc; omega), (by intro hc; omega), (by intro hc; omega),
        (by intro hc; omega), fun _ => h4 rfl⟩
    · have hnone : Sdouble[pc]? = none := by rw [List.getElem?_eq_none_iff]; simp [Sdouble]; omega
      rw [show stepP Sdouble ⟨pc, mm⟩ = ⟨pc, mm⟩ from by simp only [stepP, hnone]]
      show SdInv r pc mm
      exact ⟨hamp, h25, h3, (by intro hc; exact absurd hc (by omega)),
        (by intro hc; exact absurd hc (by omega)), (by intro hc; exact absurd hc (by omega)),
        (by intro hc; exact absurd hc (by omega)), (by intro hc; exact absurd hc hpe)⟩

theorem Sdouble_amp (r : ℕ) (m : ℕ → ℤ) (h27 : m 27 = 0) (h26 : m 26 = 1)
    (h25 : m 25 = (r:ℤ)) (h3 : m 3 = 1) (hr : 1 ≤ r)
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run Sdouble t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hinv : ∀ t, SdInv r (Run Sdouble t ⟨0, m⟩).pc (Run Sdouble t ⟨0, m⟩).mem := by
    intro t
    induction t with
    | zero => exact SdInv_init r m h27 h26 h25 h3 hm
    | succ t ih =>
      rw [Run_succ]
      have hstep := SdInv_step r hr (Run Sdouble t ⟨0, m⟩).pc (Run Sdouble t ⟨0, m⟩).mem ih
      rw [← state_pc_eq (rfl : (Run Sdouble t ⟨0, m⟩).pc = (Run Sdouble t ⟨0, m⟩).pc)] at hstep
      exact hstep
  intro t pc ms hrun i
  have hms : ms = (Run Sdouble t ⟨0, m⟩).mem :=
    congrArg State.mem (hrun.symm.trans (state_pc_eq rfl))
  rw [hms]
  exact SdInv_amp (hinv t) i

/-! ## The setup program: amplitude of the negation loop -/

theorem amp_upd {r : ℕ} {mm : ℕ → ℤ} (h : ∀ i, -1 ≤ mm i ∧ mm i ≤ Bnd r) {d : ℕ} {v : ℤ}
    (hv : -1 ≤ v ∧ v ≤ Bnd r) :
    ∀ i, -1 ≤ (Function.update mm d v) i ∧ (Function.update mm d v) i ≤ Bnd r := by
  intro i
  rcases eq_or_ne i d with rfl | hi
  · rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hi]; exact h i

theorem SiA_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ 29) : SiA mm i = mm i := by
  unfold SiA; exact Function.update_of_ne hi _ _
theorem SiB_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ 32) : SiB mm i = mm i := by
  unfold SiB; exact Function.update_of_ne hi _ _
theorem SiC_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ 33) : SiC mm i = mm i := by
  unfold SiC; exact Function.update_of_ne hi _ _
theorem SiD_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ 34) : SiD mm i = mm i := by
  unfold SiD; exact Function.update_of_ne hi _ _
theorem SiE_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ (mm 33).toNat) : SiE mm i = mm i := by
  unfold SiE; exact Function.update_of_ne hi _ _
theorem SiF_frame {mm : ℕ → ℤ} {i : ℕ} (hi : i ≠ 28) : SiF mm i = mm i := by
  unfold SiF; exact Function.update_of_ne hi _ _

/-- The negation loop carried with its amplitude bound. -/
def SiIA (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) : Prop :=
  InInv r N pj k mem ∧ (∀ i, -1 ≤ mem i ∧ mem i ≤ Bnd r)

theorem SiIA_inv {r N : ℕ} {pj : ℕ → ℕ} {k : ℕ} {mem : ℕ → ℤ} (h : SiIA r N pj k mem) :
    InInv r N pj k mem := h.1
theorem SiIA_amp {r N : ℕ} {pj : ℕ → ℕ} {k : ℕ} {mem : ℕ → ℤ} (h : SiIA r N pj k mem) :
    ∀ i, -1 ≤ mem i ∧ mem i ≤ Bnd r := h.2

theorem Sinput_stuck10 (mem : ℕ → ℤ) : ∀ t, Run Sinput t ⟨10, mem⟩ = ⟨10, mem⟩ :=
  Run_stuck_none Sinput ⟨10, mem⟩ rfl

theorem Sbody_inv (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) : InInv r N pj (k+1) (Sbody mem) := by
  have eBig : ∀ (X : ℕ), X ≤ 1000 + N → X ≠ 1000 + (N+1) + (k+1) := fun X hX => by omega
  have eBig2 : ∀ (X : ℕ), X ≤ 1000 + (N+1) + k → X ≠ 1000 + (N+1) + (k+1) := fun X hX => by omega
  have ev : ∀ i, i ≠ 28 → i ≠ 29 → i ≠ 32 → i ≠ 33 → i ≠ 34 →
      i ≠ 1000 + (N+1) + (k+1) → Sbody mem i = mem i :=
    fun i a b c d e f => Sbody_val r N pj k mem hk h a b c d e f
  have h26 : Sbody mem 26 = (2:ℤ)^r := by
    rw [ev 26 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 26 (by omega)), h.s26]
  have h30 : Sbody mem 30 = 1000 + ((N:ℤ)+1) := by
    rw [ev 30 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 30 (by omega)), h.s30]
  have hinp : ∀ j, 1 ≤ j → j ≤ N → Sbody mem (1000 + j) = (pj j : ℤ) := by
    intro j hj1 hjN
    rw [ev (1000+j) (by omega) (by omega) (by omega) (by omega) (by omega) (eBig (1000+j) (by omega)),
      h.inp j hj1 hjN]
  have hout : ∀ j, 1 ≤ j → j ≤ k + 1 → Sbody mem (1000 + (N+1) + j) = (2:ℤ)^r - (pj j : ℤ) := by
    intro j hj1 hjk
    rcases Nat.lt_or_ge j (k+1) with hjlt | hjge
    · rw [ev (1000+(N+1)+j) (by omega) (by omega) (by omega) (by omega) (by omega)
          (eBig2 (1000+(N+1)+j) (by omega)), h.out j hj1 (by omega)]
    · have hje : j = k + 1 := by omega
      subst hje
      rw [Sbody_2k r N pj k mem hk h]
  exact ⟨by rw [ev 0 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 0 (by omega)), h.s0],
    by rw [ev 1 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 1 (by omega)), h.s1],
    by rw [ev 3 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 3 (by omega)), h.s3],
    h26,
    by rw [Sbody_28 r N pj k mem hk h]; push_cast; ring,
    h30,
    by rw [ev 31 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 31 (by omega)), h.s31],
    by rw [ev 35 (by omega) (by omega) (by omega) (by omega) (by omega) (eBig 35 (by omega)), h.s35],
    hinp, hout⟩

theorem Sbody_amp_run (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : InInv r N pj k mem) (hamp : ∀ i, -1 ≤ mem i ∧ mem i ≤ Bnd r)
    (hN : 2*(N:ℤ) + 1001 ≤ Bnd r) (h2r : (2:ℤ)^r ≤ Bnd r)
    (hpr : ∀ j, 1 ≤ j → j ≤ N → (pj j : ℤ) ≤ (2:ℤ)^r) :
    ∀ t ≤ 8, ∀ pc ms, Run Sinput t ⟨2, mem⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hgt : ¬ (mem 28 > mem 35) := by rw [h.s28, h.s35]; omega
  have hkn : (k:ℤ) + 1 ≤ (N:ℤ) := by exact_mod_cast (show k + 1 ≤ N by omega)
  have hM1 : SiA mem = Function.update mem 29 (1000 + ((k:ℤ)+1)) := by
    unfold SiA; rw [h.s31, h.s28]
  have hnat29 : ((SiA mem) 29).toNat = 1000 + (k+1) := by
    rw [hM1, Function.update_self]
    have h1 : ((1000 + ((k:ℤ)+1)).toNat : ℤ) = ((1000 + (k+1) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    exact_mod_cast h1
  have hM2 : SiB (SiA mem) = Function.update (SiA mem) 32 ((pj (k+1) : ℕ) : ℤ) := by
    unfold SiB; rw [hnat29]
    congr 1
    rw [hM1, Function.update_of_ne (by omega : (1000 + (k+1) : ℕ) ≠ 29)]
    exact h.inp (k+1) (by omega) (by omega)
  have hM3 : SiC (SiB (SiA mem)) = Function.update (SiB (SiA mem)) 33 (1000 + ((N:ℤ)+1) + ((k:ℤ)+1)) := by
    unfold SiC
    rw [show (SiB (SiA mem)) 30 = mem 30 from by rw [hM2, Function.update_of_ne (by omega : (30:ℕ) ≠ 32), hM1, Function.update_of_ne (by omega : (30:ℕ) ≠ 29)]]
    rw [show (SiB (SiA mem)) 28 = mem 28 from by rw [hM2, Function.update_of_ne (by omega : (28:ℕ) ≠ 32), hM1, Function.update_of_ne (by omega : (28:ℕ) ≠ 29)]]
    rw [h.s30, h.s28]
  have hM4 : SiD (SiC (SiB (SiA mem))) =
      Function.update (SiC (SiB (SiA mem))) 34 ((2:ℤ)^r - ((pj (k+1) : ℕ) : ℤ)) := by
    unfold SiD
    rw [show (SiC (SiB (SiA mem))) 26 = mem 26 from by
      rw [hM3, Function.update_of_ne (by omega : (26:ℕ) ≠ 33), hM2, Function.update_of_ne (by omega : (26:ℕ) ≠ 32), hM1, Function.update_of_ne (by omega : (26:ℕ) ≠ 29)]]
    rw [show (SiC (SiB (SiA mem))) 32 = (pj (k+1) : ℕ) from by
      rw [hM3, Function.update_of_ne (by omega : (32:ℕ) ≠ 33), hM2, Function.update_self]]
    rw [h.s26]
  have hnat33 : ((SiD (SiC (SiB (SiA mem)))) 33).toNat = 1000 + (N+1) + (k+1) := by
    rw [hM4, Function.update_of_ne (by omega : (33:ℕ) ≠ 34), hM3, Function.update_self]
    have h1 : ((1000 + ((N:ℤ)+1) + ((k:ℤ)+1)).toNat : ℤ) = ((1000 + (N+1) + (k+1) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    exact_mod_cast h1
  have hW28 : (SiE (SiD (SiC (SiB (SiA mem))))) 28 = (k:ℤ)+1 := by
    rw [SiE_frame (by rw [hnat33]; omega), SiD_frame (by omega), SiC_frame (by omega),
      SiB_frame (by omega), SiA_frame (by omega), h.s28]
  have hW3 : (SiE (SiD (SiC (SiB (SiA mem))))) 3 = 1 := by
    rw [SiE_frame (by rw [hnat33]; omega), SiD_frame (by omega), SiC_frame (by omega),
      SiB_frame (by omega), SiA_frame (by omega), h.s3]
  -- run states
  have r1 : Run Sinput 1 ⟨2, mem⟩ = ⟨3, mem⟩ := by rw [Run_one, Si2l mem hgt]
  have r2 : Run Sinput 2 ⟨2, mem⟩ = ⟨4, SiA mem⟩ := by
    rw [show (2:ℕ) = 1+1 from rfl, Run_add, r1, Run_one, Si3]
  have r3 : Run Sinput 3 ⟨2, mem⟩ = ⟨5, SiB (SiA mem)⟩ := by
    rw [show (3:ℕ) = 2+1 from rfl, Run_add, r2, Run_one, Si4]
  have r4 : Run Sinput 4 ⟨2, mem⟩ = ⟨6, SiC (SiB (SiA mem))⟩ := by
    rw [show (4:ℕ) = 3+1 from rfl, Run_add, r3, Run_one, Si5]
  have r5 : Run Sinput 5 ⟨2, mem⟩ = ⟨7, SiD (SiC (SiB (SiA mem)))⟩ := by
    rw [show (5:ℕ) = 4+1 from rfl, Run_add, r4, Run_one, Si6]
  have r6 : Run Sinput 6 ⟨2, mem⟩ = ⟨8, SiE (SiD (SiC (SiB (SiA mem))))⟩ := by
    rw [show (6:ℕ) = 5+1 from rfl, Run_add, r5, Run_one, Si7]
  have r7 : Run Sinput 7 ⟨2, mem⟩ = ⟨9, Sbody mem⟩ := by
    rw [show (7:ℕ) = 6+1 from rfl, Run_add, r6, Run_one, Si8]; rfl
  have r8 : Run Sinput 8 ⟨2, mem⟩ = ⟨2, Sbody mem⟩ := by
    rw [show (8:ℕ) = 7+1 from rfl, Run_add, r7, Run_one, Si9]
  -- amplitude of intermediate memories
  have hv1 : -1 ≤ 1000 + ((k:ℤ)+1) ∧ 1000 + ((k:ℤ)+1) ≤ Bnd r :=
    ⟨by omega, by linarith [hN, hkn]⟩
  have hv2 : -1 ≤ ((pj (k+1) : ℕ) : ℤ) ∧ ((pj (k+1) : ℕ) : ℤ) ≤ Bnd r :=
    ⟨by omega, le_trans (hpr (k+1) (by omega) (by omega)) h2r⟩
  have hv3 : -1 ≤ 1000 + ((N:ℤ)+1) + ((k:ℤ)+1) ∧ 1000 + ((N:ℤ)+1) + ((k:ℤ)+1) ≤ Bnd r :=
    ⟨by omega, by linarith [hN, hkn]⟩
  have hv4 : -1 ≤ (2:ℤ)^r - ((pj (k+1) : ℕ) : ℤ) ∧ (2:ℤ)^r - ((pj (k+1) : ℕ) : ℤ) ≤ Bnd r :=
    ⟨by have := hpr (k+1) (by omega) (by omega); linarith, by linarith [h2r]⟩
  have a1 : ∀ i, -1 ≤ (SiA mem) i ∧ (SiA mem) i ≤ Bnd r := by
    rw [hM1]; exact amp_upd hamp hv1
  have a2 : ∀ i, -1 ≤ (SiB (SiA mem)) i ∧ (SiB (SiA mem)) i ≤ Bnd r := by
    rw [hM2]; exact amp_upd a1 hv2
  have a3 : ∀ i, -1 ≤ (SiC (SiB (SiA mem))) i ∧ (SiC (SiB (SiA mem))) i ≤ Bnd r := by
    rw [hM3]; exact amp_upd a2 hv3
  have a4 : ∀ i, -1 ≤ (SiD (SiC (SiB (SiA mem)))) i ∧ (SiD (SiC (SiB (SiA mem)))) i ≤ Bnd r := by
    rw [hM4]; exact amp_upd a3 hv4
  have a5 : ∀ i, -1 ≤ (SiE (SiD (SiC (SiB (SiA mem))))) i ∧
      (SiE (SiD (SiC (SiB (SiA mem))))) i ≤ Bnd r := by
    unfold SiE
    rw [hnat33, show (SiD (SiC (SiB (SiA mem)))) 34 = (2:ℤ)^r - ((pj (k+1) : ℕ) : ℤ) from by
      rw [hM4, Function.update_self]]
    exact amp_upd a4 hv4
  have a6 : ∀ i, -1 ≤ (Sbody mem) i ∧ (Sbody mem) i ≤ Bnd r := by
    unfold Sbody SiF
    rw [hW28, hW3]
    have hv6' : -1 ≤ ((k:ℤ)+1) + 1 ∧ ((k:ℤ)+1) + 1 ≤ Bnd r := ⟨by omega, by linarith [hN, hkn]⟩
    exact amp_upd a5 hv6'
  intro t ht pc ms hrun i
  interval_cases t
  · rw [Run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hamp i
  · rw [r1] at hrun; injection hrun with _ hms; rw [← hms]; exact hamp i
  · rw [r2] at hrun; injection hrun with _ hms; rw [← hms]; exact a1 i
  · rw [r3] at hrun; injection hrun with _ hms; rw [← hms]; exact a2 i
  · rw [r4] at hrun; injection hrun with _ hms; rw [← hms]; exact a3 i
  · rw [r5] at hrun; injection hrun with _ hms; rw [← hms]; exact a4 i
  · rw [r6] at hrun; injection hrun with _ hms; rw [← hms]; exact a5 i
  · rw [r7] at hrun; injection hrun with _ hms; rw [← hms]; exact a6 i
  · rw [r8] at hrun; injection hrun with _ hms; rw [← hms]; exact a6 i

theorem SiIA_step (r N : ℕ) (pj : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℤ) (hk : k < N)
    (h : SiIA r N pj k mem) (hN : 2*(N:ℤ) + 1001 ≤ Bnd r) (h2r : (2:ℤ)^r ≤ Bnd r)
    (hpr : ∀ j, 1 ≤ j → j ≤ N → (pj j : ℤ) ≤ (2:ℤ)^r) :
    SiIA r N pj (k+1) (Sbody mem) := by
  have hgt : ¬ (mem 28 > mem 35) := by rw [h.1.s28, h.1.s35]; omega
  exact ⟨Sbody_inv r N pj k mem hk h.1,
    Sbody_amp_run r N pj k mem hk h.1 h.2 hN h2r hpr 8 le_rfl 2 (Sbody mem)
      (Sbody_run mem hgt)⟩

theorem Sinput_amp (r N : ℕ) (pj : ℕ → ℕ) (mem : ℕ → ℤ)
    (h0 : mem 0 = (N:ℤ)+1) (h1 : mem 1 = 0) (h3 : mem 3 = 1) (h31 : mem 31 = 1000)
    (h35 : mem 35 = (N:ℤ)) (h26 : mem 26 = (2:ℤ)^r)
    (hinp : ∀ j, 1 ≤ j → j ≤ N → mem (1000+j) = (pj j : ℤ))
    (hN : 2*(N:ℤ) + 1001 ≤ Bnd r) (h2r : (2:ℤ)^r ≤ Bnd r)
    (hpr : ∀ j, 1 ≤ j → j ≤ N → (pj j : ℤ) ≤ (2:ℤ)^r)
    (hamp : ∀ i, -1 ≤ mem i ∧ mem i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run Sinput t ⟨0, mem⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hB1 : (1:ℤ) ≤ Bnd r := const_le_Bnd r 1 (by norm_num)
  have hNn : (0:ℤ) ≤ (N:ℤ) := by omega
  have h30v : Si30 mem 30 = 1000 + ((N:ℤ)+1) := by
    simp only [Si30, Function.update_self]; rw [h31, h0]
  have hAmp30 : ∀ i, -1 ≤ (Si30 mem) i ∧ (Si30 mem) i ≤ Bnd r := by
    have hv : -1 ≤ mem 31 + mem 0 ∧ mem 31 + mem 0 ≤ Bnd r := by
      rw [h31, h0]; exact ⟨by omega, by linarith [hN, hNn]⟩
    unfold Si30; exact amp_upd hamp hv
  have eS3 : (Si30 mem) 3 = mem 3 := by
    simp only [Si30]; rw [Function.update_of_ne (by decide : (3:ℕ) ≠ 30)]
  have eS1 : (Si30 mem) 1 = mem 1 := by
    simp only [Si30]; rw [Function.update_of_ne (by decide : (1:ℕ) ≠ 30)]
  have hAmp28 : ∀ i, -1 ≤ (Si28 (Si30 mem)) i ∧ (Si28 (Si30 mem)) i ≤ Bnd r := by
    have hv : -1 ≤ (Si30 mem) 3 + (Si30 mem) 1 ∧ (Si30 mem) 3 + (Si30 mem) 1 ≤ Bnd r := by
      rw [eS3, eS1, h3, h1]; exact ⟨by norm_num, by linarith [hB1]⟩
    unfold Si28
    exact amp_upd hAmp30 hv
  have h28v : Si28 (Si30 mem) 28 = (0:ℤ) + 1 := by
    simp only [Si28, Function.update_self]
    rw [eS3, eS1, h3, h1]; norm_num
  have hpre : ∀ i, i ≠ 28 → i ≠ 30 → Si28 (Si30 mem) i = mem i := by
    intro i h28 h30
    simp only [Si28, Si30]
    rw [Function.update_of_ne h28, Function.update_of_ne h30]
  have hinv : InInv r N pj 0 (Si28 (Si30 mem)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, h30v, ?_, ?_, ?_, ?_⟩
    · rw [hpre 0 (by omega) (by omega)]; exact h0
    · rw [hpre 1 (by omega) (by omega)]; exact h1
    · rw [hpre 3 (by omega) (by omega)]; exact h3
    · rw [hpre 26 (by omega) (by omega)]; exact h26
    · exact h28v
    · rw [hpre 31 (by omega) (by omega)]; exact h31
    · rw [hpre 35 (by omega) (by omega)]; exact h35
    · intro j hj1 hjN; rw [hpre (1000 + j) (by omega) (by omega)]; exact hinp j hj1 hjN
    · intro j hj1 hj0; omega
  have h2s : Run Sinput 2 ⟨0, mem⟩ = ⟨2, Si28 (Si30 mem)⟩ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Run_add, Run_one, Run_one, Si0, Si1]
  have hinv0 : SiIA r N pj 0 (Si28 (Si30 mem)) := ⟨hinv, hAmp28⟩
  have hloop : ∀ (m k : ℕ) (mm : ℕ → ℤ), k ≤ N → N - k ≤ m → SiIA r N pj k mm →
      ∀ t, ∀ pc ms, Run Sinput t ⟨2, mm⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
    intro m
    induction m with
    | zero =>
      intro k mm hk hm hSi t pc ms hrun i
      have hkN : k = N := by omega
      have hgti : mm 28 > mm 35 := by rw [hSi.1.s28, hSi.1.s35, hkN]; omega
      rcases Nat.eq_zero_or_pos t with h0t | htpos
      · subst h0t; rw [Run_zero] at hrun
        injection hrun with _ hms; rw [← hms]; exact hSi.2 i
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t-1, by omega⟩
        rw [show t'+1 = 1 + t' from by omega, Run_add, Run_one, Si2g mm hgti,
          Sinput_stuck10 mm t'] at hrun
        injection hrun with _ hms; rw [← hms]; exact hSi.2 i
    | succ m ih =>
      intro k mm hk hm hSi t pc ms hrun i
      rcases Nat.lt_or_ge k N with hlt | hge
      · have hgtn : ¬ (mm 28 > mm 35) := by rw [hSi.1.s28, hSi.1.s35]; omega
        have h8 : Run Sinput 8 ⟨2, mm⟩ = ⟨2, Sbody mm⟩ := Sbody_run mm hgtn
        rcases Nat.lt_or_ge t 8 with ht8 | ht8
        · exact Sbody_amp_run r N pj k mm hlt hSi.1 hSi.2 hN h2r hpr t (by omega) pc ms hrun i
        · obtain ⟨t', rfl⟩ : ∃ t', t = 8 + t' := ⟨t-8, by omega⟩
          rw [Run_add, h8] at hrun
          exact ih (k+1) (Sbody mm) (by omega) (by omega)
            (SiIA_step r N pj k mm hlt hSi hN h2r hpr) t' pc ms hrun i
      · have hkN : k = N := by omega
        have hgti : mm 28 > mm 35 := by rw [hSi.1.s28, hSi.1.s35, hkN]; omega
        rcases Nat.eq_zero_or_pos t with h0t | htpos
        · subst h0t; rw [Run_zero] at hrun
          injection hrun with _ hms; rw [← hms]; exact hSi.2 i
        · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t-1, by omega⟩
          rw [show t'+1 = 1 + t' from by omega, Run_add, Run_one, Si2g mm hgti,
            Sinput_stuck10 mm t'] at hrun
          injection hrun with _ hms; rw [← hms]; exact hSi.2 i
  intro t pc ms hrun i
  rcases Nat.lt_or_ge t 2 with ht2 | ht2
  · interval_cases t
    · rw [Run_zero] at hrun; injection hrun with _ hms; rw [← hms]; exact hamp i
    · rw [Run_one] at hrun; injection hrun with _ hms; rw [← hms]; exact hAmp30 i
  · obtain ⟨t', rfl⟩ : ∃ t', t = 2 + t' := ⟨t-2, by omega⟩
    rw [Run_add, h2s] at hrun
    exact hloop N 0 (Si28 (Si30 mem)) (Nat.zero_le _) (by omega) hinv0 t' pc ms hrun i

/-! ## The setup program: amplitude -/

set_option maxHeartbeats 1600000 in
theorem Sprog_amp (n r : ℕ) (pj : ℕ → ℕ) (m : ℕ → ℤ)
    (h0 : m 0 = (n:ℤ)+1) (h1 : m 1 = 0) (h2 : m 2 = 1) (h3 : m 3 = 2) (h4 : m 4 = 1000)
    (h25 : m 25 = (r:ℤ)) (hinp : ∀ j, 1 ≤ j → j ≤ n → m (1000 + j) = (pj j : ℤ))
    (hN : 2*(n:ℤ) + 1001 ≤ Bnd r) (h2r : (2:ℤ)^r ≤ Bnd r) (hr : 1 ≤ r)
    (hpr : ∀ j, 1 ≤ j → j ≤ n → (pj j : ℤ) ≤ (2:ℤ)^r)
    (hm : ∀ i, -1 ≤ m i ∧ m i ≤ Bnd r) :
    ∀ t, ∀ pc ms, Run Sprog t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hnn : (0:ℤ) ≤ (n:ℤ) := by omega
  have hnB : (n:ℤ) ≤ Bnd r := by linarith [hN]
  -- Sconst phase
  have hScAmp : ∀ t, ∀ pc ms, Run Sconst t ⟨0, m⟩ = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    fun t pc ms h => Sconst_amp n r m h0 h1 h2 h3 h4 hnB hm t pc ms h
  have hScPC : ∀ t < 13, (Run Sconst t ⟨0, m⟩).pc < Sconst.length := by
    intro t ht; rw [Sconst_length, Sconst_pc m t (by omega)]; omega
  obtain ⟨hc2, hc3, hc4, hc5, hc6, hc7, hc11, hc12, hc23, hc31, hc26, hc27, hc35, hcfr⟩ :=
    Sconst_consts n r m h1 h2 h0 h3 h4
  have hmcAmp : ∀ i, -1 ≤ (mc m) i ∧ (mc m) i ≤ Bnd r :=
    hScAmp 13 13 (mc m) (Sconst_run m)
  have mc25 : (mc m) 25 = (r:ℤ) := by
    rw [hcfr 25 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h25
  have mc0 : (mc m) 0 = (n:ℤ)+1 := by
    rw [hcfr 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h0
  have mc1 : (mc m) 1 = 0 := by
    rw [hcfr 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h1
  have mcInp : ∀ j, 1 ≤ j → j ≤ n → (mc m) (1000 + j) = m (1000 + j) := by
    intro j hj1 hjn
    exact hcfr (1000 + j) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- Sdouble phase
  have hSdAmp : ∀ t, ∀ pc ms, Run Sdouble t ⟨0, mc m⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Sdouble_amp r (mc m) hc27 hc26 mc25 hc3 hr hmcAmp
  have hSdPC : ∀ t < 4*r + 1, (Run Sdouble t ⟨0, mc m⟩).pc < Sdouble.length := by
    intro t ht; rw [show Sdouble.length = 4 from rfl]
    exact Sdouble_pc_lt (mc m) r hc27 mc25 hc3 t ht
  obtain ⟨mfin, hrunSd, hfin26, hfin27, hfinfr⟩ :=
    Sdouble_run r (mc m) r mc25 (by rw [hc27]; ring) hc3
  have hrunSd' : Run Sdouble (4*r + 1) ⟨0, mc m⟩ = ⟨Sdouble.length, mfin⟩ := hrunSd
  have hfin26' : mfin 26 = (2:ℤ)^r := by rw [hfin26, hc26]; ring
  have hfin27' : mfin 27 = (r:ℤ) := hfin27
  have hfinAmp : ∀ i, -1 ≤ mfin i ∧ mfin i ≤ Bnd r := by
    intro i
    rcases eq_or_ne i 26 with rfl | h26ne
    · rw [hfin26']
      exact ⟨by have : (0:ℤ) ≤ (2:ℤ)^r := pow_nonneg (by norm_num) _; omega, h2r⟩
    · rcases eq_or_ne i 27 with rfl | h27ne
      · rw [hfin27']
        exact ⟨by omega, r_le_Bnd r hr⟩
      · rw [hfinfr i h26ne h27ne]; exact hmcAmp i
  have hfin0 : mfin 0 = (n:ℤ)+1 := by rw [hfinfr 0 (by omega) (by omega), mc0]
  have hfin1 : mfin 1 = 0 := by rw [hfinfr 1 (by omega) (by omega), mc1]
  have hfin3 : mfin 3 = 1 := by rw [hfinfr 3 (by omega) (by omega), hc3]
  have hfin31 : mfin 31 = 1000 := by rw [hfinfr 31 (by omega) (by omega), hc31]
  have hfin35 : mfin 35 = (n:ℤ) := by rw [hfinfr 35 (by omega) (by omega), hc35]
  have hfinInp : ∀ j, 1 ≤ j → j ≤ n → mfin (1000 + j) = (pj j : ℤ) := by
    intro j hj1 hjn
    rw [hfinfr (1000 + j) (by omega) (by omega), mcInp j hj1 hjn]
    exact hinp j hj1 hjn
  -- Sinput phase
  have hSiAmp : ∀ t, ∀ pc ms, Run Sinput t ⟨0, mfin⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Sinput_amp r n pj mfin hfin0 hfin1 hfin3 hfin31 hfin35 hfin26' hfinInp hN h2r hpr hfinAmp
  have hSdSiAmp : ∀ t, ∀ pc ms, Run (Sdouble ++ shiftProg Sdouble.length Sinput) t ⟨0, mc m⟩
      = ⟨pc, ms⟩ → ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Run_concat_amp Sdouble Sinput (4*r + 1) ⟨0, mc m⟩ mfin r hSdPC hrunSd' hSdAmp hSiAmp
  have hAll : ∀ t, ∀ pc ms, Run (Sconst ++ shiftProg Sconst.length
        (Sdouble ++ shiftProg Sdouble.length Sinput)) t ⟨0, m⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Run_concat_amp Sconst (Sdouble ++ shiftProg Sdouble.length Sinput) 13 ⟨0, m⟩ (mc m) r
      hScPC (by rw [Sconst_length]; exact Sconst_run m) hScAmp hSdSiAmp
  exact hAll

/-! ## Amplitude of the merged program of Theorem 1 -/

theorem Th1_aux_amp (n r : ℕ) (hr : 3 ≤ r) (hn : 1 ≤ n)
    (hpr : ∀ j, 1 ≤ j → j ≤ n → Nat.nth Nat.Prime j < 2^r) :
    ∀ t, ∀ pc ms, Run (Th1prog n) t ⟨0, m0 n r⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := by
  have hr1 : 1 ≤ r := by omega
  have hprn : Nat.nth Nat.Prime n < 2^r := hpr n hn le_rfl
  have hN : 2*(n:ℤ) + 1001 ≤ Bnd r := two_n_add_le_Bnd n r hn hr1 hprn
  have h2r : (2:ℤ)^r ≤ Bnd r := two_pow_le_Bnd r hr1
  -- the prime generator phase
  have hAmpA : ∀ t, ∀ pc ms, Run (prog.take 19) t ⟨0, m0 n r⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r := prime_amp n r hn hr1 hprn
  obtain ⟨TA, hTA, mA, hA, hpcA, hA25, hAout, hA0, hA1, hA2, hA3, hA4, hAz⟩ := first_part n r
  set pj : ℕ → ℕ := fun j => Nat.nth Nat.Prime j with hpj
  have hprj : ∀ j, 1 ≤ j → j ≤ n → (pj j : ℤ) ≤ (2:ℤ)^r := by
    intro j hj1 hjn
    have h := hpr j hj1 hjn
    rw [hpj]; exact_mod_cast (le_of_lt h)
  have hAout' : ∀ j, 1 ≤ j → j ≤ n → mA (1000 + j) = (pj j : ℤ) :=
    fun j hj1 hjn => hAout j (by omega)
  -- the setup phase
  obtain ⟨TB, hTB, mB, hB, hpcB, hB2, hB3, hB4, hB5, hB6, hB7, hB11, hB12, hB23, hB25, hB26,
      hBinp, hBneg, hBfr⟩ :=
    Sprog_first n r pj mA hA0 hA1 hA2 hA3 hA4 hA25 hAout'
  have hAmpMAB : ∀ i, -1 ≤ mA i ∧ mA i ≤ Bnd r := hAmpA TA 19 mA hA
  have hAmpB : ∀ t, ∀ pc ms, Run Sprog t ⟨0, mA⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Sprog_amp n r pj mA hA0 hA1 hA2 hA3 hA4 hA25 hAout' hN h2r hr1 hprj hAmpMAB
  have hBinn : ∀ j, 1 ≤ j → j ≤ n → mB (1000 + j) = (Nat.nth Nat.Prime j : ℤ) :=
    fun j hj1 hjn => hBinp j hj1 hjn
  have hBnegn : ∀ j, 1 ≤ j → j ≤ n →
      mB (1000 + (n+1) + j) = (2:ℤ)^r - (Nat.nth Nat.Prime j : ℤ) :=
    fun j hj1 hjn => hBneg j hj1 hjn
  -- the logarithm phase
  obtain ⟨TC, hTC, mC, hC, hpcC, hClog, hCfr, hC2, hC3, hC4, hC5, hC6, hC7, hC11, hC12, hC23⟩ :=
    Nprog_first r hr (inpList n) mB hB25 hB2 hB3 hB4 hB5 hB6 hB7 hB11 hB12 hB23
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega, by omega⟩)
      (inpList_nodup n)
      (fun p hp p' hp' => inpList_disj hp hp')
      (fun p hp p' hp' hne => inpList_disj2 hp hp' hne)
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        have ho := (nth_prime_odd_lt hj1).1
        have h1 := (nth_prime_odd_lt hj1).2
        have hlt := hpr j hj1 hjn
        have hqle : Nat.nth Nat.Prime j ≤ 2^r := le_of_lt hlt
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Nat.nth Nat.Prime j, ho, h1, hlt, hBinn j hj1 hjn⟩
        · refine ⟨2^r - Nat.nth Nat.Prime j, odd_two_pow_sub (by omega) ho hqle, by omega,
            by omega, ?_⟩
          rw [hBnegn j hj1 hjn, Nat.cast_sub hqle]; push_cast; ring)
  have hAmpMBB : ∀ i, -1 ≤ mB i ∧ mB i ≤ Bnd r := hAmpB TB 27 mB hB
  have hAmpC : ∀ t, ∀ pc ms, Run (Nprog (inpList n)) t ⟨0, mB⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Nprog_amp r hr (inpList n) mB hB25 hB2 hB3 hB4 hB5 hB6 hB7 hB11 hB12 hB23
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega, by omega⟩)
      (inpList_nodup n)
      (fun p hp p' hp' => inpList_disj hp hp')
      (fun p hp p' hp' hne => inpList_disj2 hp hp' hne)
      (fun p hp => by
        obtain ⟨j, hj1, hjn, hj⟩ := inpList_mem hp
        have ho := (nth_prime_odd_lt hj1).1
        have h1 := (nth_prime_odd_lt hj1).2
        have hlt := hpr j hj1 hjn
        have hqle : Nat.nth Nat.Prime j ≤ 2^r := le_of_lt hlt
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Nat.nth Nat.Prime j, ho, h1, hlt, hBinn j hj1 hjn⟩
        · refine ⟨2^r - Nat.nth Nat.Prime j, odd_two_pow_sub (by omega) ho hqle, by omega,
            by omega, ?_⟩
          rw [hBnegn j hj1 hjn, Nat.cast_sub hqle]; push_cast; ring)
      hAmpMBB
  -- the selector phase
  obtain ⟨TD, hTD, mD, hD, hpcD, hDout, hDfr⟩ := Sel_first n mC hC3
  have hAmpMCC : ∀ i, -1 ≤ mC i ∧ mC i ≤ Bnd r := hAmpC TC (Nprog (inpList n)).length mC hC
  have hsum : ∀ j, 1 ≤ j → j ≤ n →
      -1 ≤ mC (1000 + 2*(n+1) + j) + mC (1000 + 3*(n+1) + j) ∧
      mC (1000 + 2*(n+1) + j) + mC (1000 + 3*(n+1) + j) ≤ (2:ℤ)^(r-2) - 1 := by
    intro j hj1 hjn
    have hp1 := inpList_mem_first hj1 hjn
    have hp2 := inpList_mem_second hj1 hjn
    have hlt := hpr j hj1 hjn
    have h1 := (nth_prime_odd_lt hj1).2
    have hodd : BkSet.oddPrime (j-1) = Nat.nth Nat.Prime j := by
      simp only [BkSet.oddPrime]; congr 1; omega
    have ho1 : LogSpec r (BkSet.oddPrime (j-1)) (mC (1000 + 2*(n+1) + j)) := by
      have hh := hClog _ hp1 (Nat.nth Nat.Prime j) (nth_prime_odd_lt hj1).1 (nth_prime_odd_lt hj1).2
        hlt (hBinn j hj1 hjn)
      rwa [← hodd] at hh
    have ho2 : LogSpec r (2^r - BkSet.oddPrime (j-1)) (mC (1000 + 3*(n+1) + j)) := by
      have hqle : Nat.nth Nat.Prime j ≤ 2^r := le_of_lt hlt
      have hh := hClog _ hp2 (2^r - Nat.nth Nat.Prime j)
        (odd_two_pow_sub (by omega) (nth_prime_odd_lt hj1).1 hqle) (by omega) (by omega)
        (by rw [hBnegn j hj1 hjn, Nat.cast_sub hqle]; push_cast; ring)
      rwa [← hodd] at hh
    have hph : BkSet.oddPrime (j-1) ≤ 2^r := by rw [hodd]; exact le_of_lt hlt
    have heq := out_eq_hh r (by omega) (j-1) _ _ hph ho1 ho2
    have hhZ : (BkSet.hh r (by omega) (j-1) : ℤ) ≤ (2:ℤ)^(r-2) - 1 := by
      have h := (BkSet.hh r (by omega) (j-1)).isLt
      have hc : ((BkSet.hh r (by omega) (j-1) : ℕ) : ℤ) < (2:ℤ)^(r-2) := by exact_mod_cast h
      omega
    exact ⟨by linarith [heq], by linarith [heq, hhZ]⟩
  have hAmpD : ∀ t, ∀ pc ms, Run (Sel n) t ⟨0, mC⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Sel_amp n r hr1 mC hC3 hAmpMCC hsum
  -- glue
  have hx1 : ∀ t, ∀ pc ms, Run (x1 n) t ⟨0, mB⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Run_concat_amp (Nprog (inpList n)) (Sel n) TC ⟨0, mB⟩ mC r hpcC hC hAmpC hAmpD
  have hx2 : ∀ t, ∀ pc ms, Run (x2 n) t ⟨0, mA⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd r :=
    Run_concat_amp Sprog (x1 n) TB ⟨0, mA⟩ mB r hpcB
      (by rw [Sprog_length]; exact hB) hAmpB hx1
  have H := Run_concat_amp (prog.take 19) (x2 n) TA ⟨0, m0 n r⟩ mA r hpcA
    (by rw [take19_len]; exact hA) hAmpA hx2
  rw [take19_len] at H
  exact H

theorem theorem1_amp (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ∀ t, ∀ pc ms, Run (Th1prog n) t ⟨0, m0 n (BkSet.rOf n k)⟩ = ⟨pc, ms⟩ →
      ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd (BkSet.rOf n k) := by
  have hr3 : 3 ≤ BkSet.rOf n k := three_le_rOf n k hk
  have hpr : ∀ j, 1 ≤ j → j ≤ n → Nat.nth Nat.Prime j < 2^(BkSet.rOf n k) := by
    intro j hj1 hjn
    have := oddPrime_lt_two_rOf n k (by omega) (j-1) (by omega)
    simpa only [BkSet.oddPrime, Nat.sub_add_cancel hj1] using this
  exact Th1_aux_amp n (BkSet.rOf n k) hr3 hn hpr

/-- **Theorem 1, combined form.**  For all `n ≥ 1`, `k ≥ 2`, the merged
program `Th1prog n` runs on the integer RAM machine from `m0 n r` (`r = 1 + ⌈k log₂ p_n⌉`)
for at most `O(n^4) + 2n·O(r^2)` elementary steps, halts with register
`1000 + 4*(n+1) + i` holding the canonical exponent `h_i` of the `i`-th odd prime (so it
computes `H[n,k]`), and every register stays inside `-1 .. 2^(2r) + O(1)` throughout. -/
theorem theorem1_full (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ∃ (T : ℕ) (mem : ℕ → ℤ),
      T ≤ 700 * (n + 2)^4 + 100 + (4 * BkSet.rOf n k + 8*n + 17)
          + (2*n) * (18 + (40*(BkSet.rOf n k + 1)*(BkSet.rOf n k + 1) + 100))
          + 2*n ∧
      Run (Th1prog n) T ⟨0, m0 n (BkSet.rOf n k)⟩ = ⟨(Th1prog n).length, mem⟩ ∧
      (∀ i, i < n →
        mem (1000 + 4*(n+1) + (i+1)) =
          ((BkSet.hh (BkSet.rOf n k)
            (BkSet.rOf_ge_two n k (le_trans (by norm_num) hk)) i : ℕ) : ℤ)) ∧
      (∀ t, ∀ pc ms, Run (Th1prog n) t ⟨0, m0 n (BkSet.rOf n k)⟩ = ⟨pc, ms⟩ →
          ∀ i, -1 ≤ ms i ∧ ms i ≤ Bnd (BkSet.rOf n k)) := by
  have hr3 : 3 ≤ BkSet.rOf n k := three_le_rOf n k hk
  have hr2 : 2 ≤ BkSet.rOf n k := BkSet.rOf_ge_two n k (le_trans (by norm_num) hk)
  have hpr : ∀ j, 1 ≤ j → j ≤ n → Nat.nth Nat.Prime j < 2^(BkSet.rOf n k) := by
    intro j hj1 hjn
    have := oddPrime_lt_two_rOf n k (by omega) (j-1) (by omega)
    simpa only [BkSet.oddPrime, Nat.sub_add_cancel hj1] using this
  obtain ⟨TA, TB, TC, TD, mD, hrun, hTA, hTB, hTC, hTD, hlog1, hlog2, hsum⟩ :=
    Th1_aux n (BkSet.rOf n k) hr3 hpr
  refine ⟨TA + (TB + (TC + TD)), mD, ?_, hrun, ?_, Th1_aux_amp n (BkSet.rOf n k) hr3 hn hpr⟩
  · have hlen : (inpList n).length = 2*n := inpList_length n
    rw [hlen] at hTC; omega
  · intro i hi
    have hj1 : 1 ≤ i+1 := by omega
    have hjn : i+1 ≤ n := by omega
    have hp : BkSet.oddPrime i ≤ 2^(BkSet.rOf n k) := by
      have := oddPrime_lt_two_rOf n k (by omega) i hi; omega
    have hl1 : LogSpec (BkSet.rOf n k) (BkSet.oddPrime i) (mD (1000 + 2*(n+1) + (i+1))) := by
      simpa only [BkSet.oddPrime] using hlog1 (i+1) hj1 hjn
    have hl2 : LogSpec (BkSet.rOf n k) (2^(BkSet.rOf n k) - BkSet.oddPrime i)
        (mD (1000 + 3*(n+1) + (i+1))) := by
      simpa only [BkSet.oddPrime] using hlog2 (i+1) hj1 hjn
    rw [hsum (i+1) hj1 hjn]
    exact out_eq_hh (BkSet.rOf n k) hr2 i _ _ hp hl1 hl2

end BkSet.RAM

end
