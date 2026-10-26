import Mathlib

/-!
# Self-contained statement and proof of Sergeev's Theorem 1

***This file has no dependencies other than Mathlib.*** 

Reference: I. S. Sergeev, *A lower bound on the monotone switching complexity of
the threshold function `T_{n-1}^n`*, Discrete Math. Appl. **35** (2025), 327–330.
-/

/-!
# Monotone switching networks, connectivity functions and switching complexity

This file formalizes the basic definitions from the theory of switching networks,
following the first paragraph of the introduction of

* I. S. Sergeev, *A lower bound on the monotone switching complexity of the
  threshold function `T_{n-1}^n`*, Discrete Math. Appl. **35** (2025), 327–330.

A switching network is a graph whose edges are labelled by Boolean variables or
their negations.  Here we formalize the **monotone** model, in which negations are
forbidden, and we only consider **2-pole** networks, i.e. networks with two
distinguished vertices (the poles).  Such a network implements a single Boolean
function, its *connectivity function* between the two poles.

## Main definitions

* `Switching.Network` — a monotone switching network: an undirected multigraph
  whose edges are labelled by variables from `α`.
* `Switching.Network.Walk` — a walk (path) in such a network.
* `Switching.Network.Connects` — the connectivity predicate between two vertices.
* `Switching.Network.connFun` — the connectivity function (a Boolean function).
* `Switching.Network.Implements` — a network implements a Boolean function.
* `Switching.Network.complexity` — the number of edges of a network.
* `Switching.switchingComplexity` — the minimal complexity of a network
  implementing a given Boolean function.

## Notes on the model

* Multiple edges between the same pair of vertices are allowed, as in the paper
  (the graph "admits multiple edges connecting a pair of vertices").
* Working with *walks* rather than simple paths does not change the connectivity
  function: the conjunction of edge labels along a walk is implied by the
  conjunction along the simple path contained in it, and both are disjoined over
  all walks resp. paths.
-/

namespace Switching

open Classical

open scoped ENat

/-- A **(monotone) switching network** on the vertex type `V` and edge type `E`,
whose edges carry labels from the variable set `α`.

This is an undirected multigraph: every edge `e` has two endpoints `src e` and
`tgt e`, and several edges may share the same pair of endpoints.  Since we work in
the monotone model, a label is simply a variable; negations are not allowed. -/
structure Network (α V E : Type) where
  src : E → V
  tgt : E → V
  lab : E → α

namespace Network

variable {α V E : Type}

/-- A **walk** in a switching network `G`: a sequence of edges each of which
connects the previous vertex to the next one, traversed in either direction
(the network is undirected). -/
inductive Walk (G : Network α V E) : V → V → Type where
  | nil (v : V) : Walk G v v
  | cons {u v w : V} (e : E)
      (h : (G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u))
      (p : Walk G v w) : Walk G u w

/-- The list of edges traversed by a walk, in order. -/
def Walk.edges {G : Network α V E} {u v : V} : Walk G u v → List E
  | .nil _ => []
  | .cons e _ p => e :: p.edges

/-- The **connectivity function of a walk** evaluated at an assignment `x`: the
product (conjunction) of the labels of the edges of the walk.  Concretely it is
`true` iff every edge of the walk carries a variable that is true under `x`. -/
def Walk.eval {G : Network α V E} {u v : V} (p : Walk G u v) (x : α → Bool) : Bool :=
  p.edges.all fun e => x (G.lab e)

@[simp] theorem Walk.eval_nil {G : Network α V E} (v : V) (x : α → Bool) :
    (Walk.nil (G := G) v).eval x = true := rfl

theorem Walk.eval_eq_true_iff {G : Network α V E} {u v : V} (p : Walk G u v)
    (x : α → Bool) : p.eval x = true ↔ ∀ e ∈ p.edges, x (G.lab e) = true := by
  simp [Walk.eval, List.all_eq_true]

/-- Two vertices `s` and `t` are **connected** under the assignment `x` if some
walk from `s` to `t` uses only edges whose labels are true under `x`.  This is the
connectivity function of the pair `(s, t)`: the disjunction, over all walks from
`s` to `t`, of the connectivity functions of those walks. -/
def Connects (G : Network α V E) (s t : V) (x : α → Bool) : Prop :=
  ∃ p : Walk G s t, p.eval x = true

theorem connects_iff_exists_walk {G : Network α V E} {s t : V} {x : α → Bool} :
    Connects G s t x ↔ ∃ p : Walk G s t, ∀ e ∈ p.edges, x (G.lab e) = true := by
  simp only [Connects, Walk.eval_eq_true_iff]

/-- The connectivity predicate is monotone in the assignment: making more
variables true can only help. -/
theorem Connects.mono {G : Network α V E} {s t : V} {x y : α → Bool}
    (hxy : ∀ a, x a = true → y a = true) (h : Connects G s t x) : Connects G s t y := by
  obtain ⟨p, hp⟩ := h
  rw [Walk.eval_eq_true_iff] at hp
  exact ⟨p, (Walk.eval_eq_true_iff p y).mpr fun e he => hxy _ (hp e he)⟩

/-- The trivial walk shows that every vertex is connected to itself. -/
theorem connects_self (G : Network α V E) (s : V) (x : α → Bool) : Connects G s s x :=
  ⟨Walk.nil s, rfl⟩

end Network

/-- A Boolean function on the variable set `α`, i.e. a map `𝔹^α → 𝔹`. -/
abbrev BoolFun (α : Type) := (α → Bool) → Bool

namespace Network

variable {α V E : Type}

/-- The **connectivity function** between two vertices `s` and `t` of a switching
network `G`: it maps an assignment to `true` iff `s` and `t` are connected in the
subnetwork spanned by the edges whose labels are true under that assignment. -/
noncomputable def connFun (G : Network α V E) (s t : V) : BoolFun α :=
  fun x => if Connects G s t x then true else false

@[simp] theorem connFun_eq_true_iff {G : Network α V E} {s t : V} {x : α → Bool} :
    connFun G s t x = true ↔ Connects G s t x := by
  unfold connFun
  by_cases h : Connects G s t x <;> simp [h]

/-- `G` **implements** the Boolean function `f` between the poles `s` and `t` if
`f` is the connectivity function of `G` between `s` and `t`. -/
def Implements (G : Network α V E) (s t : V) (f : BoolFun α) : Prop :=
  ∀ x, f x = true ↔ Connects G s t x

theorem implements_iff_eq_connFun {G : Network α V E} {s t : V} {f : BoolFun α} :
    Implements G s t f ↔ f = connFun G s t := by
  constructor
  · intro h
    funext x
    by_cases hc : Connects G s t x
    · rw [(h x).mpr hc, connFun_eq_true_iff.mpr hc]
    · have hf : f x = false := by
        cases hfx : f x with
        | false => rfl
        | true => exact absurd hfx (fun ht => hc ((h x).mp ht))
      have hc' : connFun G s t x = false := by
        cases hcx : connFun G s t x with
        | false => rfl
        | true => exact absurd hcx (fun ht => hc (connFun_eq_true_iff.mp ht))
      rw [hf, hc']
  · intro h x
    rw [h, connFun_eq_true_iff]

/-- Every network implements its own connectivity function. -/
theorem implements_self (G : Network α V E) (s t : V) :
    Implements G s t (connFun G s t) :=
  implements_iff_eq_connFun.mpr rfl

set_option linter.unusedVariables false in
/-- The **complexity** of a switching network is the number of its edges
(switches). -/
def complexity (G : Network α V E) [Fintype E] : ℕ :=
  Fintype.card E

end Network

/-- A **2-pole** switching network: a switching network together with two
distinguished, *distinct* vertices, the poles `s` and `t`.  Such a network
implements a single Boolean function, its connectivity function between the two
poles. -/
structure TwoPole (α V E : Type) extends Network α V E where
  s : V
  t : V
  hst : s ≠ t

namespace TwoPole

variable {α V E : Type}

/-- The connectivity function implemented by the 2-pole network `N`. -/
noncomputable def connFun (N : TwoPole α V E) : BoolFun α :=
  N.toNetwork.connFun N.s N.t

/-- The 2-pole network `N` implements the Boolean function `f`. -/
def Implements (N : TwoPole α V E) (f : BoolFun α) : Prop :=
  N.toNetwork.Implements N.s N.t f

/-- The complexity of the 2-pole network `N` is the number of its edges. -/
def complexity (N : TwoPole α V E) [Fintype E] : ℕ :=
  N.toNetwork.complexity

/-- Every 2-pole network implements its own connectivity function. -/
theorem implements_self (N : TwoPole α V E) : N.Implements N.connFun :=
  Network.implements_self N.toNetwork N.s N.t

end TwoPole

/-- The **switching complexity** of a Boolean function `f`, valued in `ℕ∞`: the
infimum of the number of edges over all (finite, monotone) 2-pole switching
networks implementing `f`.  It is `⊤` exactly when `f` is not implementable by
such a network (equivalently, when `f` fails to be monotone or fails to vanish on
the all-false assignment).

Restricting to vertex type `Fin k` and edge type `Fin m` is no loss of generality:
any finite network can be relabelled by finite ordinals. -/
noncomputable def switchingComplexity (f : BoolFun α) : ℕ∞ :=
  sInf { c : ℕ∞ | ∃ (k m : ℕ) (N : TwoPole α (Fin k) (Fin m)),
    N.Implements f ∧ c = (m : ℕ∞) }

/-- Any 2-pole network with `m` edges implementing `f` yields an upper bound on
the switching complexity of `f`. -/
theorem switchingComplexity_le {α : Type} {f : BoolFun α} {k m : ℕ}
    {N : TwoPole α (Fin k) (Fin m)} (h : N.Implements f) :
    switchingComplexity f ≤ (m : ℕ∞) :=
  sInf_le ⟨k, m, N, h, rfl⟩

end Switching


/-!
# Proofs for monotone switching networks

* `Switching.Network.lemma1` — **Lemma 1** of the paper: a parity ("handshake")
  lemma about paths joining two vertices and a set of edges meeting each path an
  even number of times.

## Proof strategy for Lemma 1

Write `F` for the distinguished set of edges.  Suppose, for contradiction, that
`t` is not reachable from `s` using only edges outside `F`, and let `χ` be the
indicator of the vertices reachable from `s` avoiding `F` (valued in `ℤ/2`).

1. The set of reachable vertices is closed under edges outside `F`
   (`ConnectsAvoiding.tgt_of_src`, `ConnectsAvoiding.src_of_tgt`), so every edge
   outside `F` has both endpoints on the same side of the cut defined by `χ`.
2. For a walk `p` from `s` to `t`, the sum `∑_{e ∈ p.edges} (χ (src e) + χ (tgt e))`
   telescopes to `χ s + χ t = 1` (`walkSum_eq`): every walk from a vertex of the
   cut to its complement crosses the cut an odd number of times.
3. Summing this over the `m` paths gives `∑_i 1 = m ≡ 1 (mod 2)`, since `m` is odd.
4. On the other hand, reindexing the double sum by edges (using that the paths are
   acyclic, so each edge occurs at most once per path) expresses the same quantity
   as `∑_{e ∈ F} c e · (#paths through e)`, and each `#paths through e` is even by
   hypothesis, while `c e = 0` for `e ∉ F`.  Hence the total is `0 (mod 2)`.

The two computations contradict each other, so `t` *is* reachable from `s`
avoiding `F`.

The argument does not use the paper's normalization `G = ⋃ p_i`: extra edges are
harmless, because the cut is defined by reachability in the whole network.
-/

namespace Switching

open Classical

/-! ## Auxiliary facts about `List`/`Finset` sums -/

/-- For a nodup list, the list sum of a function equals the `Finset` sum over its
elements. -/
theorem sum_map_eq_toFinset_sum {β α : Type} [AddCommMonoid β] [DecidableEq α]
    (f : α → β) : ∀ {l : List α}, l.Nodup → (l.map f).sum = l.toFinset.sum f
  | [], _ => by simp
  | a :: l, h => by
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp h
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert (by rw [List.mem_toFinset]; exact ha)]
      rw [sum_map_eq_toFinset_sum f hl]

/-- Grouping: `∑ i, if e ∈ l i then c e else 0` counts, weighted by `c e`, the
indices `i` with `e ∈ l i`. -/
theorem sum_ite_mem_eq {E ι : Type} [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (c : E → ZMod 2) (l : ι → List E) (e : E) :
    (∑ i : ι, (if e ∈ l i then c e else 0))
      = ((Finset.univ.filter (fun i => e ∈ l i)).card : ZMod 2) * c e := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

namespace Network

variable {α V E : Type}

/-! ## Walks -/

/-- Concatenation of walks: if `p : Walk G a b` and `q : Walk G b c`, then
`p.append q : Walk G a c`. -/
def Walk.append {G : Network α V E} : ∀ {a b c : V}, Walk G a b → Walk G b c → Walk G a c
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e h p', q => .cons e h (p'.append q)

/-- The edge list of a concatenation is the concatenation of the edge lists. -/
@[simp] theorem Walk.edges_append {G : Network α V E} {a b c : V}
    (p : Walk G a b) (q : Walk G b c) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil v => simp [Walk.append, Walk.edges]
  | cons e h p' ih => simp [Walk.append, Walk.edges, ih]

/-! ## Connectivity avoiding a set of edges -/

/-- `s` and `t` are connected by a walk whose edges all lie outside `F`. -/
def ConnectsAvoiding (G : Network α V E) (F : E → Prop) (a b : V) : Prop :=
  ∃ p : Walk G a b, ∀ e ∈ p.edges, ¬ F e

/-- The set of vertices reachable from `s` avoiding `F` is closed under edges
outside `F`: an edge `e ∉ F` with `G.src e` reachable has its other endpoint
`G.tgt e` reachable too. -/
theorem ConnectsAvoiding.tgt_of_src {G : Network α V E} {F : E → Prop} {s : V} {e : E}
    (he : ¬ F e) (h : ConnectsAvoiding G F s (G.src e)) :
    ConnectsAvoiding G F s (G.tgt e) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.append (.cons e (Or.inl ⟨rfl, rfl⟩) (.nil (G.tgt e))), ?_⟩
  rw [Walk.edges_append]
  intro e' he'
  rcases List.mem_append.mp he' with h' | h'
  · exact hp e' h'
  · simp only [Walk.edges, List.mem_cons, List.not_mem_nil, or_false] at h'
    subst h'
    exact he

/-- Symmetric form of `ConnectsAvoiding.tgt_of_src`: an edge `e ∉ F` with
`G.tgt e` reachable has `G.src e` reachable too. -/
theorem ConnectsAvoiding.src_of_tgt {G : Network α V E} {F : E → Prop} {s : V} {e : E}
    (he : ¬ F e) (h : ConnectsAvoiding G F s (G.tgt e)) :
    ConnectsAvoiding G F s (G.src e) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.append (.cons e (Or.inr ⟨rfl, rfl⟩) (.nil (G.src e))), ?_⟩
  rw [Walk.edges_append]
  intro e' he'
  rcases List.mem_append.mp he' with h' | h'
  · exact hp e' h'
  · simp only [Walk.edges, List.mem_cons, List.not_mem_nil, or_false] at h'
    subst h'
    exact he

/-! ## The parity computation -/

/-- The number of traversals of `F`-relevant edges along a walk, weighted by a
coefficient `c`, i.e. `∑_{e ∈ q.edges} c e` (counted with multiplicity). -/
def walkSum {G : Network α V E} (c : E → ZMod 2) {a b : V} (q : Walk G a b) : ZMod 2 :=
  (q.edges.map c).sum

/-- **Telescoping.**  If `c e = χ (G.src e) + χ (G.tgt e)` for a vertex weight `χ`,
then `walkSum c q = χ a + χ b`: along a walk from `a` to `b` the intermediate
weights cancel in pairs. -/
theorem walkSum_eq {G : Network α V E} (c : E → ZMod 2) (χ : V → ZMod 2)
    (hc : ∀ e, c e = χ (G.src e) + χ (G.tgt e)) :
    ∀ {a b : V} (q : Walk G a b), walkSum c q = χ a + χ b := fun q =>
  Walk.rec (motive := fun a b t => walkSum c t = χ a + χ b)
    (fun v => by
      simp only [walkSum, Walk.edges, List.map_nil, List.sum_nil]
      exact (CharTwo.add_self_eq_zero (χ v)).symm)
    (fun {u v w} e h p ih => by
      have heq : c e = χ u + χ v := by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hc e, h1, h2]
        · rw [hc e, h1, h2, add_comm]
      simp only [walkSum, Walk.edges, List.map_cons, List.sum_cons] at ih ⊢
      rw [heq, ih, add_assoc, ← add_assoc (χ v), CharTwo.add_self_eq_zero, zero_add])
    q

/-! ## Lemma 1 -/

/-- **Lemma 1** (Sergeev).  Let `G` be a graph, `F` a set of edges, and
`p_0, …, p_{m-1}` **acyclic** walks (no edge is traversed twice, hypothesis
`hsimple`) joining `s` and `t`, where `m` is **odd**.  If every edge of `F` lies on
an **even** number of the walks `p_i`, then `s` and `t` are connected by a walk
avoiding every edge of `F`.

The paper states this as a statement about a graph `G = ⋃ p_i`; here `G` is an
arbitrary switching network, which is stronger but equally true (see the file
header).  The number of paths through an edge is measured with multiplicity in the
path index `i`, i.e. `#{i | e ∈ (p i).edges}`. -/
theorem lemma1 {G : Network α V E} [DecidableEq E] {F : E → Prop} {s t : V} {m : ℕ}
    (hm : Odd m) (p : Fin m → Walk G s t)
    (hsimple : ∀ i, (p i).edges.Nodup)
    (hF : ∀ e, F e → Even ((Finset.univ.filter (fun i : Fin m => e ∈ (p i).edges)).card)) :
    ConnectsAvoiding G F s t := by
  by_contra hcon
  -- Indicator of the vertices reachable from `s` avoiding `F`.
  let χ : V → ZMod 2 := fun v => if ConnectsAvoiding G F s v then 1 else 0
  have hχs : χ s = 1 := by
    have h : ConnectsAvoiding G F s s := ⟨Walk.nil s, by intro e he; simp [Walk.edges] at he⟩
    simp only [χ]; rw [ite_eq_left h]
  have hχt : χ t = 0 := by simp only [χ]; rw [ite_eq_right hcon]
  let c : E → ZMod 2 := fun e => χ (G.src e) + χ (G.tgt e)
  have hc : ∀ e, c e = χ (G.src e) + χ (G.tgt e) := fun e => rfl
  -- Edges outside `F` do not cross the cut `χ`.
  have hcF : ∀ e, ¬ F e → c e = 0 := by
    intro e he
    have hiff : ConnectsAvoiding G F s (G.src e) ↔ ConnectsAvoiding G F s (G.tgt e) :=
      ⟨fun h => h.tgt_of_src he, fun h => h.src_of_tgt he⟩
    have hχ : χ (G.src e) = χ (G.tgt e) := by
      simp only [χ]
      by_cases hsl : ConnectsAvoiding G F s (G.src e)
      · rw [ite_eq_left hsl, ite_eq_left (hiff.mp hsl)]
      · rw [ite_eq_right hsl, ite_eq_right (fun h => hsl (hiff.mpr h))]
    rw [hc, hχ, CharTwo.add_self_eq_zero]
  -- First computation: each path contributes `1`, hence the total is `m ≡ 1`.
  have hsum1 : ∑ i : Fin m, walkSum c (p i) = 1 := by
    have h1 : ∀ i, walkSum c (p i) = 1 := fun i => by
      rw [walkSum_eq c χ hc (p i), hχs, hχt, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simp [hm.natCast_zmod_two]
  -- Second computation: reindexing by edges gives a sum of even terms, hence `0`.
  have hsum2 : ∑ i : Fin m, walkSum c (p i) = 0 := by
    let U : Finset E := Finset.univ.biUnion (fun i : Fin m => (p i).edges.toFinset)
    have hstepA : ∀ i, walkSum c (p i) = ∑ e ∈ U, (if e ∈ (p i).edges then c e else 0) := by
      intro i
      have hsub : (p i).edges.toFinset ⊆ U :=
        Finset.subset_biUnion_of_mem (fun i : Fin m => (p i).edges.toFinset) (Finset.mem_univ i)
      have h1 : (p i).edges.toFinset.sum c
          = (p i).edges.toFinset.sum (fun e => if e ∈ (p i).edges then c e else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        have hmem : e ∈ (p i).edges := by simpa [List.mem_toFinset] using he
        rw [ite_eq_left hmem]
      have h2 : (p i).edges.toFinset.sum (fun e => if e ∈ (p i).edges then c e else 0)
          = ∑ e ∈ U, (if e ∈ (p i).edges then c e else 0) := by
        apply Finset.sum_subset hsub
        intro x _ hxnot
        have hmem : x ∉ (p i).edges := by simpa [List.mem_toFinset] using hxnot
        rw [ite_eq_right hmem]
      rw [walkSum, sum_map_eq_toFinset_sum c (hsimple i), h1, h2]
    rw [Finset.sum_congr rfl (fun i _ => hstepA i), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun e _ => ?_)
    by_cases hFe : F e
    · have hite : ∑ i : Fin m, (if e ∈ (p i).edges then c e else 0)
          = ((Finset.univ.filter (fun i : Fin m => e ∈ (p i).edges)).card : ZMod 2) * c e :=
        sum_ite_mem_eq c (fun i => (p i).edges) e
      rw [hite, (hF e hFe).natCast_zmod_two, zero_mul]
    · show (∑ i : Fin m, (if e ∈ (p i).edges then c e else 0)) = 0
      simp [hcF e hFe]
  rw [hsum1] at hsum2
  exact absurd hsum2 (by decide)

end Network

end Switching

/-! ## Acyclic reduction of walks

A walk that repeats a vertex contains a closed sub-walk; cutting that sub-walk
out yields a shorter walk whose edge set is contained in the original one.
Iterating, every walk can be replaced by an *acyclic* walk — one without repeated
vertices, hence without repeated edges — whose edges are a subset of the original
edges.

This is point (3) of the strategy for Theorem 1.  The connectivity function of a
network is the disjunction, over all walks, of the conjunction of their edge
labels; and since an acyclic reduction `W₀` of a walk `W₁` satisfies
`W₀.edges ⊆ W₁.edges` (as sets), the disjunct attached to `W₁` is implied by the
one attached to `W₀`.  Hence only acyclic walks are needed to describe the
connectivity function.
-/

namespace Switching
namespace Network

variable {α V E : Type}

/-- The list of vertices visited by a walk, in order. -/
@[simp] def Walk.verts {G : Network α V E} : {u v : V} → Walk G u v → List V
  | _, _, .nil v => [v]
  | u, _, .cons _ _ p => u :: p.verts

@[simp] theorem Walk.verts_nil {G : Network α V E} (v : V) :
    (Walk.nil (G := G) v).verts = [v] := rfl

theorem Walk.verts_cons {G : Network α V E} {u v w : V} (e : E)
    (h : (G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u)) (p : Walk G v w) :
    (Walk.cons e h p).verts = u :: p.verts := rfl

/-- The starting vertex of a walk is one of the vertices it visits. -/
theorem Walk.head_mem_verts {G : Network α V E} {u v : V} (W : Walk G u v) : u ∈ W.verts :=
  Walk.rec (motive := fun {u v : V} W => u ∈ W.verts)
    (fun v => by simp)
    (fun e h p ih => by simp) W

/-- Any walk can be split at an occurrence of one of its vertices: if
`a ∈ W.verts`, then `W = q₁.append q₂` with `q₁` a walk ending at `a` and `q₂` a
walk starting at `a`. -/
theorem Walk.exists_append_of_mem_verts {G : Network α V E} {u v : V} (W : Walk G u v)
    (a : V) (ha : a ∈ W.verts) :
    ∃ q₁ : Walk G u a, ∃ q₂ : Walk G a v, W = q₁.append q₂ :=
  Walk.rec (motive := fun {u v : V} W => ∀ (a : V), a ∈ W.verts →
      ∃ q₁ : Walk G u a, ∃ q₂ : Walk G a v, W = q₁.append q₂)
    (fun v a ha => by
      rw [Walk.verts_nil, List.mem_singleton] at ha
      subst ha
      exact ⟨.nil _, .nil _, rfl⟩)
    (fun e h p ih a ha => by
      rw [Walk.verts_cons, List.mem_cons] at ha
      rcases ha with ha | ha
      · subst ha
        exact ⟨.nil _, .cons e h p, rfl⟩
      · obtain ⟨q₁, q₂, hq⟩ := ih a ha
        exact ⟨.cons e h q₁, q₂, by simp [Walk.append, hq]⟩)
    W a ha

/-- Both endpoints of every edge traversed by a walk are vertices visited by that
walk. -/
theorem Walk.mem_verts_of_mem_edges {G : Network α V E} {u v : V} (W : Walk G u v) :
    ∀ {e : E}, e ∈ W.edges → G.src e ∈ W.verts ∧ G.tgt e ∈ W.verts :=
  Walk.rec (motive := fun {u v : V} W => ∀ {e : E}, e ∈ W.edges →
      G.src e ∈ W.verts ∧ G.tgt e ∈ W.verts)
    (fun v e he => by simp [Walk.edges] at he)
    (fun e' h' p' ih e he => by
      rw [Walk.edges, List.mem_cons] at he
      rcases he with heq | he
      · subst heq
        rw [Walk.verts_cons]
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by rw [h1]; exact List.mem_cons_self ..,
                 by rw [h2]; exact List.mem_cons_of_mem _ (Walk.head_mem_verts p')⟩
        · exact ⟨by rw [h1]; exact List.mem_cons_of_mem _ (Walk.head_mem_verts p'),
                 by rw [h2]; exact List.mem_cons_self ..⟩
      · obtain ⟨hs, ht⟩ := ih he
        exact ⟨List.mem_cons_of_mem _ hs, List.mem_cons_of_mem _ ht⟩)
    W

/-- Every walk either is acyclic (`W.verts` has no repeats) or contains a closed
sub-walk, i.e. has the form `p₁.append (loop.append p₂)` with `loop` a non-empty
closed walk. -/
theorem Walk.verts_nodup_or_split {G : Network α V E} {u v : V} (W : Walk G u v) :
    W.verts.Nodup ∨ ∃ (w : V) (p₁ : Walk G u w) (p₂ : Walk G w v) (loop : Walk G w w),
      W = p₁.append (loop.append p₂) ∧ loop.edges ≠ [] :=
  Walk.rec (motive := fun {u v : V} W => W.verts.Nodup ∨
      ∃ (w : V) (p₁ : Walk G u w) (p₂ : Walk G w v) (loop : Walk G w w),
        W = p₁.append (loop.append p₂) ∧ loop.edges ≠ [])
    (fun v => Or.inl (by simp))
    (fun {u' v' w' : V} e h p ih => by
      rw [Walk.verts_cons]
      rcases ih with hnp | ⟨w, p₁, p₂, loop, hEq, hloop⟩
      · by_cases hu : u' ∈ p.verts
        · obtain ⟨q₁, q₂, hq⟩ := Walk.exists_append_of_mem_verts p u' hu
          refine Or.inr ⟨u', .nil u', q₂, .cons e h q₁, ?_, ?_⟩
          · simp [Walk.append, hq]
          · simp [Walk.edges]
        · exact Or.inl (List.nodup_cons.mpr ⟨hu, hnp⟩)
      · refine Or.inr ⟨w, .cons e h p₁, p₂, loop, ?_, hloop⟩
        simp [Walk.append, hEq])
    W

/-- An acyclic walk traverses every edge at most once. -/
theorem Walk.nodup_edges_of_verts_nodup {G : Network α V E} {u v : V} (W : Walk G u v)
    (h : W.verts.Nodup) : W.edges.Nodup :=
  Walk.rec (motive := fun {u v : V} W => W.verts.Nodup → W.edges.Nodup)
    (fun v h => by simp [Walk.edges])
    (fun e h' p ih h => by
      rw [Walk.verts_cons] at h
      obtain ⟨hup, hp⟩ := List.nodup_cons.mp h
      rw [Walk.edges]
      refine List.nodup_cons.mpr ⟨?_, ih hp⟩
      intro he
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hup (h1 ▸ (Walk.mem_verts_of_mem_edges p he).1)
      · exact hup (h2 ▸ (Walk.mem_verts_of_mem_edges p he).2))
    W h

/-- **Acyclic reduction.**  Every walk `W` can be replaced by an acyclic walk `W'`
with the same endpoints, whose edges satisfy every property `P` that holds on all
edges of `W` (in particular `W'.edges ⊆ W.edges`).  Proved by strong induction on
the number of edges, cutting out a closed sub-walk whenever one exists. -/
theorem Walk.exists_nodup_edges {G : Network α V E} {u v : V} (W : Walk G u v) (P : E → Prop)
    (hP : ∀ e ∈ W.edges, P e) :
    ∃ W' : Walk G u v, W'.edges.Nodup ∧ ∀ e ∈ W'.edges, P e := by
  have h : ∀ n, ∀ {u v : V} (W : Walk G u v) (P : E → Prop), W.edges.length = n →
      (∀ e ∈ W.edges, P e) → ∃ W' : Walk G u v, W'.edges.Nodup ∧ ∀ e ∈ W'.edges, P e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v W P hlen hP
      rcases Walk.verts_nodup_or_split W with hnodup | ⟨w, p₁, p₂, loop, hEq, hloop⟩
      · exact ⟨W, Walk.nodup_edges_of_verts_nodup W hnodup, hP⟩
      · have hlen' : (p₁.append p₂).edges.length < n := by
          rw [← hlen, hEq]
          simp only [Walk.edges_append, List.length_append]
          have hpos : 0 < loop.edges.length := List.length_pos_iff.mpr hloop
          omega
        have hP' : ∀ e ∈ (p₁.append p₂).edges, P e := by
          intro e he
          apply hP
          rw [hEq, Walk.edges_append, Walk.edges_append]
          rw [Walk.edges_append] at he
          simp only [List.mem_append] at he ⊢
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inr he)
        exact ih _ hlen' (p₁.append p₂) P rfl hP'
  exact h W.edges.length W P rfl hP

end Network
end Switching


/-!
# Theorem 1: a lower bound on the monotone switching complexity of `T_{n-1}^n`

This file formalizes the proof of Theorem 1 of

* I. S. Sergeev, *A lower bound on the monotone switching complexity of the
  threshold function `T_{n-1}^n`*, Discrete Math. Appl. **35** (2025), 327–330.

## Main results

* `Switching.thresholdFun` — the threshold function `T_k^n`.
* `Switching.counting_lemma` — the combinatorial core of Theorem 1
  (part II of the paper's proof).
* `Switching.Network.complexity_lower_bound` — Theorem 1 for a network *presented*
  by `n` acyclic pole-to-pole walks `p i` avoiding the variable `x_i` (parts I–III
  of the paper's proof).
* `Switching.theorem1` — **Theorem 1 stated for an arbitrary network**, with no
  structural hypothesis: the `n` acyclic `x_i`-free walks are *derived* from the
  sole assumption that the network computes `T_{n-1}^n` (using the acyclic
  reduction of walks `Walk.exists_nodup_edges` of `ContactThresh.Proofs`).
* `Switching.switchingComplexity_threshold_ge` — the same lower bound phrased
  directly as `K⁺(T_{n-1}^n) ≥ (n - (2k-1)!) · log₂ k`.
-/

namespace Switching

open Classical

/-! ## The threshold function -/

/-- The number of variables carrying the value `true` in the assignment `x`. -/
noncomputable def ones {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- The **threshold function** `T_k^n`: it takes the value `1` on an assignment
`x : Fin n → Bool` if and only if at least `k` of its arguments equal `1`. -/
noncomputable def thresholdFun (k n : ℕ) : BoolFun (Fin n) :=
  fun x => decide (k ≤ ones x)

@[simp] theorem thresholdFun_eq_true_iff {k n : ℕ} {x : Fin n → Bool} :
    thresholdFun k n x = true ↔ k ≤ ones x := by
  unfold thresholdFun
  rw [decide_eq_true_eq]

/-! ## The combinatorial core (part II of the paper) -/

/-- Combinatorial data underlying Theorem 1: a square matrix `A` whose entries
are finite sets of switches, indexed by a finite type `ι`.  `HasForbidden A`
records the presence of a `2 × 3` submatrix of the shape
`(∅ a a; b ∅ b)` up to permutation of the columns, which is precisely the
configuration ruled out in part I of the paper's proof. -/
def HasForbidden {ι E : Type} (A : ι → ι → Finset E) : Prop :=
  ∃ r₁ r₂ : ι, r₁ ≠ r₂ ∧ ∃ c₁ c₂ c₃ : ι,
    c₁ ≠ c₂ ∧ c₃ ≠ c₁ ∧ c₃ ≠ c₂ ∧
    A r₁ c₁ = ∅ ∧ A r₂ c₂ = ∅ ∧ A r₁ c₃ = A r₁ c₂ ∧ A r₂ c₃ = A r₂ c₁

/-- The class of matrices `𝒜` from the paper: all diagonal entries are empty,
all off-diagonal entries are non-empty, and no forbidden submatrix occurs. -/
def IsGood {ι E : Type} (A : ι → ι → Finset E) : Prop :=
  (∀ i, A i i = ∅) ∧ (∀ i j, i ≠ j → A i j ≠ ∅) ∧ ¬ HasForbidden A

/-- The number `μ(A,i)` of distinct sets in the `i`-th row of `A`. -/
noncomputable def mu {ι E : Type} [Fintype ι] [DecidableEq E]
    (A : ι → ι → Finset E) (i : ι) : ℕ :=
  ((Finset.univ : Finset ι).image (A i)).card

end Switching

namespace Switching

/-! ### Auxiliary lemmas for the counting argument -/

/-- The image over the `Finset.univ` of a subtype is the image over the
underlying finset. -/
theorem image_univ_subtype {ι E : Type} [Fintype ι] [DecidableEq ι] [DecidableEq E]
    (S : Finset ι) (f : ι → Finset E) :
    ((Finset.univ : Finset {x // x ∈ S}).image (fun b => f b.1)) = S.image f := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b.1, b.2, hb⟩
  · rintro ⟨j, hj, hjv⟩; exact ⟨⟨j, hj⟩, hjv⟩

/-- The row diversity of a restricted (sub)matrix at `i` computes the number of
distinct values of `A i ·` over the columns of `S`. -/
theorem mu_subtype {ι E : Type} [Fintype ι] [DecidableEq ι] [DecidableEq E]
    (A : ι → ι → Finset E) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    mu (fun a b : {x // x ∈ S} => A a.1 b.1) ⟨i, hi⟩ = (S.image (fun j => A i j)).card := by
  unfold mu
  change ((Finset.univ : Finset {x // x ∈ S}).image (fun b => A i b.1)).card
      = (S.image (fun j => A i j)).card
  rw [image_univ_subtype S (fun j => A i j)]

/-- In a non-empty index type every row has diversity at least one. -/
theorem one_le_mu {ι E : Type} [Fintype ι] [DecidableEq E] (h : Nonempty ι)
    (A : ι → ι → Finset E) (i : ι) :
    1 ≤ mu A i := by
  unfold mu
  obtain ⟨j⟩ := h
  exact Finset.card_pos.mpr ⟨A i j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩

/-- Elementary factorial estimate used in the final arithmetic. -/
theorem factorial_mul_add_one_le (k : ℕ) :
    k * (2 * k).factorial + 1 ≤ (2 * k + 1).factorial := by
  rw [Nat.factorial_succ (2 * k)]
  nlinarith [Nat.factorial_pos (2 * k)]

/-- The family of statements proved by induction: for every finite index type
`ι`, every good `A : ι → ι → Finset E` and every `n = #ι` with `(2k)! ≤ n`, the
number of rows of small diversity is at most `(2k-1)!`. -/
private def CountingGoal (k : ℕ) : Prop :=
  ∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [DecidableEq E] (A : ι → ι → Finset E),
    IsGood A → (2 * k).factorial ≤ Fintype.card ι →
    ((Finset.univ : Finset ι).filter (fun i => mu A i < k)).card ≤ (2 * k - 1).factorial

end Switching

namespace Switching

/-- **Combinatorial core of Theorem 1** (part II of the paper's proof).

Let `A` be a matrix whose diagonal entries are empty, whose off-diagonal
entries are non-empty, and which contains no forbidden `(∅ a a; b ∅ b)`
submatrix.  If the index set has at least `(2k)!` elements, then all but at most
`(2k-1)!` rows contain at least `k` distinct sets. -/
theorem counting_lemma : ∀ k : ℕ, 1 ≤ k → CountingGoal k := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro hK
    unfold CountingGoal
    intro ι E _ _ _ A hA hn
    by_cases hK1 : K = 1
    · rw [hK1] at hn ⊢
      have hne : Nonempty ι := Fintype.card_pos_iff.mp (by
        have h2 : 2 ≤ Fintype.card ι := by simpa using hn
        omega)
      have hempty : (Finset.univ.filter (fun i => mu A i < 1)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _
        exact not_lt.mpr (one_le_mu hne A i)
      rw [hempty]
      simp
    · have hK2 : 2 ≤ K := by omega
      by_cases hB : (Finset.univ.filter (fun i => mu A i < K)) = ∅
      · rw [hB]; exact Nat.zero_le _
      · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hB
        rw [Finset.mem_filter] at hr
        have hrlt : mu A r < K := hr.2
        have hrir : r ∈ (Finset.univ : Finset ι) := Finset.mem_univ r
        set V : Finset ι := (Finset.univ : Finset ι).erase r with hV
        set G : Finset (Finset E) := V.image (A r) with hG
        set Sf : Finset E → Finset ι := fun v => V.filter (fun j => A r j = v) with hSf
        have hmV : ∀ i, i ∈ V ↔ i ≠ r := by
          intro i; rw [hV, Finset.mem_erase]; exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ i⟩⟩
        -- G.card + 1 ≤ K
        have hGcard : G.card + 1 ≤ K := by
          have h1 : G.card ≤ mu A r := by
            unfold mu
            apply Finset.card_le_card
            intro v hv
            rw [hG] at hv
            rcases Finset.mem_image.mp hv with ⟨j, -, rfl⟩
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
          omega
        -- subset
        have hsub : (Finset.univ.filter (fun i => mu A i < K)) ⊆
            insert r (G.biUnion (fun v => (Sf v).filter (fun i => mu A i < K))) := by
          intro i hi
          rw [Finset.mem_filter] at hi
          by_cases hir : i = r
          · rw [Finset.mem_insert]; exact Or.inl hir
          · rw [Finset.mem_insert]; right
            rw [Finset.mem_biUnion]
            refine ⟨A r i, ?_, ?_⟩
            · rw [hG]; exact Finset.mem_image.mpr ⟨i, (hmV i).mpr hir, rfl⟩
            · rw [Finset.mem_filter]
              refine ⟨?_, hi.2⟩
              change i ∈ V.filter (fun j => A r j = A r i)
              rw [Finset.mem_filter]
              exact ⟨(hmV i).mpr hir, rfl⟩
        -- disjointness
        have hdisj : ∀ v ∈ G, ∀ w ∈ G, v ≠ w →
            Disjoint ((Sf v).filter (fun i => mu A i < K))
              ((Sf w).filter (fun i => mu A i < K)) := by
          intro v _ w _ hvw
          rw [Finset.disjoint_left]
          intro i hiv hiw
          rw [Finset.mem_filter] at hiv hiw
          simp only [hSf, Finset.mem_filter] at hiv hiw
          exact hvw (hiv.1.2.symm.trans hiw.1.2)
        -- per-group bound
        have hgroup : ∀ v ∈ G,
            ((Sf v).filter (fun i => mu A i < K)).card ≤ (2 * (K - 1)).factorial := by
          intro v _
          by_cases hbig : (2 * (K - 1)).factorial ≤ (Sf v).card
          · set Sv : Finset ι := Sf v with hSv
            set Av : {i // i ∈ Sv} → {i // i ∈ Sv} → Finset E := fun a b => A a.1 b.1 with hAv
            have hgl : ∀ j k : ι, j ∈ Sv → k ∈ Sv → j ≠ k → A j r ≠ A j k := by
              intro j k hjSv hkSv hjk heq
              have hj' : j ∈ V ∧ A r j = v := by
                simp only [hSv, hSf, Finset.mem_filter] at hjSv; exact hjSv
              have hk' : k ∈ V ∧ A r k = v := by
                simp only [hSv, hSf, Finset.mem_filter] at hkSv; exact hkSv
              rw [hmV] at hj' hk'
              apply hA.2.2
              refine ⟨r, j, ?_, r, j, k, ?_, ?_, ?_, hA.1 r, hA.1 j, ?_, ?_⟩
              · exact fun h => hj'.1 h.symm
              · exact fun h => hj'.1 h.symm
              · exact hk'.1
              · exact fun h => hjk h.symm
              · rw [hk'.2, hj'.2]
              · exact heq.symm
            have hAvgood : IsGood Av := by
              refine ⟨?_, ?_, ?_⟩
              · intro a; simp only [hAv]; exact hA.1 a.1
              · intro a b hab; simp only [hAv]
                exact hA.2.1 a.1 b.1 (fun h => hab (Subtype.ext h))
              · intro hforb; apply hA.2.2
                rcases hforb with ⟨r₁, r₂, hr12, c₁, c₂, c₃, hc12, hc31, hc32, h1, h2, h3, h4⟩
                refine ⟨r₁.1, r₂.1, (fun h => hr12 (Subtype.ext h)),
                  c₁.1, c₂.1, c₃.1, (fun h => hc12 (Subtype.ext h)),
                  (fun h => hc31 (Subtype.ext h)), (fun h => hc32 (Subtype.ext h)),
                  ?_, ?_, ?_, ?_⟩
                · simpa only [hAv] using h1
                · simpa only [hAv] using h2
                · simpa only [hAv] using h3
                · simpa only [hAv] using h4
            have hcardSv : Fintype.card {i // i ∈ Sv} = Sv.card := by
              rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
            have hbound : ((Finset.univ : Finset {i // i ∈ Sv}).filter
                  (fun a => mu Av a < K - 1)).card ≤ (2 * (K - 1) - 1).factorial :=
              ih (K - 1) (by omega) (by omega) Av hAvgood (by rw [hcardSv, hSv]; exact hbig)
            calc ((Sf v).filter (fun i => mu A i < K)).card
                ≤ ((Finset.univ : Finset {i // i ∈ Sv}).filter
                    (fun a => mu Av a < K - 1)).card := by
                  refine le_trans (Finset.card_le_card ?_)
                    (Finset.card_image_le (s := (Finset.univ : Finset {i // i ∈ Sv}).filter
                        (fun a => mu Av a < K - 1)) (f := fun a : {i // i ∈ Sv} => a.1))
                  intro i hi
                  rw [Finset.mem_filter] at hi
                  obtain ⟨hiSv, hiK⟩ := hi
                  have hiSv' : i ∈ Sv := hiSv
                  have hir : i ≠ r := (hmV i).mp (by
                    simp only [hSv, hSf, Finset.mem_filter] at hiSv'; exact hiSv'.1)
                  have hmem : mu Av ⟨i, hiSv'⟩ < K - 1 := by
                    have h1 : 1 + mu Av ⟨i, hiSv'⟩ ≤ mu A i := by
                      have hmu : mu Av ⟨i, hiSv'⟩ = (Sv.image (fun j => A i j)).card := by
                        rw [hAv]; exact mu_subtype A Sv i hiSv'
                      rw [hmu]
                      unfold mu
                      have hnotin : A i r ∉ Sv.image (fun j => A i j) := by
                        intro hmem2
                        rcases Finset.mem_image.mp hmem2 with ⟨j, hjSv, hji⟩
                        have hji' : j ≠ i := by
                          intro hji_eq
                          rw [hji_eq] at hji
                          exact hA.2.1 i r hir (hji ▸ hA.1 i)
                        exact hgl i j hiSv' hjSv (fun h => hji' h.symm) hji.symm
                      calc 1 + (Sv.image (fun j => A i j)).card
                          = (insert (A i r) (Sv.image (fun j => A i j))).card := by
                            rw [Finset.card_insert_of_notMem hnotin]; omega
                        _ ≤ ((Finset.univ : Finset ι).image (A i)).card := by
                            apply Finset.card_le_card
                            intro w hw
                            rcases Finset.mem_insert.mp hw with rfl | hw'
                            · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
                            · rcases Finset.mem_image.mp hw' with ⟨j, -, rfl⟩
                              exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
                    omega
                  exact Finset.mem_image.mpr
                    ⟨⟨i, hiSv'⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmem⟩, rfl⟩
              _ ≤ (2 * (K - 1) - 1).factorial := hbound
              _ ≤ (2 * (K - 1)).factorial := Nat.factorial_le (by omega)
          · have hlt : (Sf v).card < (2 * (K - 1)).factorial := Nat.lt_of_not_le hbig
            have := Finset.card_le_card (Finset.filter_subset (fun i => mu A i < K) (Sf v))
            omega
        have hsum : (G.biUnion (fun v => (Sf v).filter (fun i => mu A i < K))).card
            ≤ G.card * (2 * (K - 1)).factorial := by
          rw [Finset.card_biUnion hdisj]
          calc ∑ v ∈ G, ((Sf v).filter (fun i => mu A i < K)).card
              ≤ ∑ v ∈ G, (2 * (K - 1)).factorial := Finset.sum_le_sum (fun v hv => hgroup v hv)
            _ = G.card * (2 * (K - 1)).factorial := by
                rw [Finset.sum_const, smul_eq_mul]
        calc (Finset.univ.filter (fun i => mu A i < K)).card
            ≤ (insert r (G.biUnion (fun v => (Sf v).filter (fun i => mu A i < K)))).card :=
              Finset.card_le_card hsub
          _ ≤ (G.biUnion (fun v => (Sf v).filter (fun i => mu A i < K))).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ G.card * (2 * (K - 1)).factorial + 1 := Nat.add_le_add_right hsum 1
          _ ≤ (2 * K - 1).factorial := by
              have hle1 : G.card ≤ K - 1 := by omega
              have h2 := factorial_mul_add_one_le (K - 1)
              have h3 : 2 * (K - 1) + 1 = 2 * K - 1 := by omega
              rw [← h3]
              exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hle1) 1) h2

end Switching

namespace Switching

/-! ## The assignment with exactly two `false` coordinates and related facts -/

/-- The assignment that is `false` exactly at the coordinates `i` and `j`. -/
def twoZero {n : ℕ} (i j : Fin n) : Fin n → Bool := fun m => decide (m ≠ i ∧ m ≠ j)

theorem twoZero_apply {n : ℕ} {i j m : Fin n} :
    twoZero i j m = true ↔ m ≠ i ∧ m ≠ j := by
  simp [twoZero]

theorem ones_twoZero {n : ℕ} {i j : Fin n} (hij : i ≠ j) : ones (twoZero i j) = n - 2 := by
  unfold ones
  have hset : (Finset.univ.filter (fun m : Fin n => twoZero i j m = true))
      = ((Finset.univ : Finset (Fin n)).erase i).erase j := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, twoZero,
      decide_eq_true_eq, and_true]
    tauto
  rw [hset]
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    rw [Finset.mem_erase]; exact ⟨hij.symm, Finset.mem_univ j⟩
  rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The assignment whose only false coordinate is `i`. -/
def singleZero {n : ℕ} (i : Fin n) : Fin n → Bool := fun m => decide (m ≠ i)

theorem singleZero_apply {n : ℕ} {i m : Fin n} : singleZero i m = true ↔ m ≠ i := by
  simp [singleZero]

/-- The assignment with a single false coordinate `i` has exactly `n - 1` true coordinates. -/
theorem ones_singleZero {n : ℕ} (i : Fin n) : ones (singleZero i) = n - 1 := by
  unfold ones
  have hset : (Finset.univ.filter (fun m : Fin n => singleZero i m = true))
      = (Finset.univ : Finset (Fin n)).erase i := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, singleZero,
      decide_eq_true_eq]
    tauto
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

namespace Network

variable {n : ℕ} {V E : Type}

/-- The set of **switches of the variable `i`** occurring along the walk `p`. -/
def switchSet [DecidableEq E] {s t : V} (G : Network (Fin n) V E) (p : Walk G s t)
    (i : Fin n) : Finset E :=
  p.edges.toFinset.filter (fun e => G.lab e = i)

theorem mem_switchSet [DecidableEq E] {G : Network (Fin n) V E} {s t : V} {p : Walk G s t}
    {i : Fin n} {e : E} :
    e ∈ switchSet G p i ↔ e ∈ p.edges ∧ G.lab e = i := by
  rw [switchSet, Finset.mem_filter, List.mem_toFinset]

theorem switchSet_eq_empty_iff [DecidableEq E] {G : Network (Fin n) V E} {s t : V}
    {p : Walk G s t} {i : Fin n} :
    (switchSet G p i = ∅) ↔ ∀ e ∈ p.edges, G.lab e ≠ i := by
  constructor
  · intro h e he heq
    have hmem : e ∈ switchSet G p i := mem_switchSet.mpr ⟨he, heq⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    rw [mem_switchSet] at he
    exact h e he.1 he.2

end Network

end Switching

namespace Switching
namespace Network

variable {n : ℕ} {V E : Type} [DecidableEq E]

/-- **Part I of Theorem 1.**  In a monotone 2-pole network computing the
threshold function `T_{n-1}^n`, consider acyclicity paths `p j` from `s` to `t`
such that `p j` avoids the switches of the variable `j` (this models the paper's
reduction: the minimal network is the union of `n` paths, the `j`-th of which
avoids `x_j`).  Then the matrix `A i j = (switches of x_i on p_j)` belongs to the
class `𝒜`: its diagonal is empty, its off-diagonal entries are non-empty, and it
contains no forbidden `(∅ a a; b ∅ b)` submatrix. -/
theorem isGood_matrix {G : Network (Fin n) V E} {s t : V} (hn : 2 ≤ n)
    (hImpl : Network.Implements G s t (thresholdFun (n - 1) n))
    (p : Fin n → Walk G s t)
    (hacyc : ∀ i, (p i).edges.Nodup)
    (havoid : ∀ i, ∀ e ∈ (p i).edges, G.lab e ≠ i) :
    IsGood (fun i j : Fin n => switchSet G (p j) i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact switchSet_eq_empty_iff.mpr (havoid i)
  · intro i j hij hemp
    have hnoi : ∀ e ∈ (p j).edges, G.lab e ≠ i := switchSet_eq_empty_iff.mp hemp
    have hnoj : ∀ e ∈ (p j).edges, G.lab e ≠ j := havoid j
    have hconn : Connects G s t (twoZero i j) := by
      rw [connects_iff_exists_walk]
      exact ⟨p j, fun e he => by
        rw [twoZero_apply]
        exact ⟨hnoi e he, hnoj e he⟩⟩
    have hval := (hImpl (twoZero i j)).mpr hconn
    rw [thresholdFun_eq_true_iff, ones_twoZero hij] at hval
    omega
  · rintro ⟨r₁, r₂, hr12, c₁, c₂, c₃, hc12, hc31, hc32, h1, h2, h3, h4⟩
    -- h1 : switchSet G (p c₁) r₁ = ∅, h2 : switchSet G (p c₂) r₂ = ∅
    -- h3 : switchSet G (p c₃) r₁ = switchSet G (p c₂) r₁
    -- h4 : switchSet G (p c₃) r₂ = switchSet G (p c₁) r₂
    have h1' : switchSet G (p c₁) r₁ = ∅ := by simpa only [] using h1
    have h2' : switchSet G (p c₂) r₂ = ∅ := by simpa only [] using h2
    have h3' : switchSet G (p c₃) r₁ = switchSet G (p c₂) r₁ := by simpa only [] using h3
    have h4' : switchSet G (p c₃) r₂ = switchSet G (p c₁) r₂ := by simpa only [] using h4
    let q : Fin 3 → Walk G s t :=
      fun k => if k = 0 then p c₁ else if k = 1 then p c₂ else p c₃
    have hq0 : q 0 = p c₁ := by simp [q]
    have hq1 : q 1 = p c₂ := by simp [q]
    have hq2 : q 2 = p c₃ := by simp [q]
    have hsimple : ∀ k : Fin 3, (q k).edges.Nodup := by
      intro k; fin_cases k
      · simpa [q] using hacyc c₁
      · simpa [q] using hacyc c₂
      · simpa [q] using hacyc c₃
    have hFeven : ∀ e, (G.lab e = r₁ ∨ G.lab e = r₂) →
        Even ((Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)).card) := by
      intro e he
      rcases he with he | he
      · have hp1 : e ∉ (p c₁).edges := fun hmem =>
          (switchSet_eq_empty_iff.mp h1) e hmem he
        have hp23 : e ∈ (p c₂).edges ↔ e ∈ (p c₃).edges := by
          constructor
          · intro hmem
            have : e ∈ switchSet G (p c₃) r₁ := by
              rw [h3']; exact mem_switchSet.mpr ⟨hmem, he⟩
            exact (mem_switchSet.mp this).1
          · intro hmem
            have : e ∈ switchSet G (p c₂) r₁ := by
              rw [← h3']; exact mem_switchSet.mpr ⟨hmem, he⟩
            exact (mem_switchSet.mp this).1
        have hSsub : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))
            ⊆ ({1, 2} : Finset (Fin 3)) := by
          intro k hk
          rw [Finset.mem_filter] at hk
          fin_cases k
          · exfalso; exact absurd (by simpa [q] using hk.2) hp1
          · simp
          · simp
        have hS01 : ((1 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)))
            ↔ ((2 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq1, hq2]
          exact hp23
        by_cases h1m : (1 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))
        · have h2m := hS01.mp h1m
          have hSeq : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) = {1, 2} := by
            apply Finset.Subset.antisymm hSsub
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact h1m
            · exact h2m
          rw [hSeq]; exact ⟨1, rfl⟩
        · have h2m : (2 : Fin 3) ∉ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) :=
            fun hc => h1m (hS01.mpr hc)
          have hSeq : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨x, hx⟩
            have hs := hSsub hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hs
            rcases hs with rfl | rfl
            · exact h1m hx
            · exact h2m hx
          rw [hSeq]; exact ⟨0, rfl⟩
      · have hp2 : e ∉ (p c₂).edges := fun hmem =>
          (switchSet_eq_empty_iff.mp h2) e hmem he
        have hp13 : e ∈ (p c₁).edges ↔ e ∈ (p c₃).edges := by
          constructor
          · intro hmem
            have : e ∈ switchSet G (p c₃) r₂ := by
              rw [h4']; exact mem_switchSet.mpr ⟨hmem, he⟩
            exact (mem_switchSet.mp this).1
          · intro hmem
            have : e ∈ switchSet G (p c₁) r₂ := by
              rw [← h4']; exact mem_switchSet.mpr ⟨hmem, he⟩
            exact (mem_switchSet.mp this).1
        have hSsub : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))
            ⊆ ({0, 2} : Finset (Fin 3)) := by
          intro k hk
          rw [Finset.mem_filter] at hk
          fin_cases k
          · simp
          · exfalso; exact absurd (by simpa [q] using hk.2) hp2
          · simp
        have hS02 : ((0 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)))
            ↔ ((2 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq0, hq2]
          exact hp13
        by_cases h0m : (0 : Fin 3) ∈ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges))
        · have h2m := hS02.mp h0m
          have hSeq : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) = {0, 2} := by
            apply Finset.Subset.antisymm hSsub
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact h0m
            · exact h2m
          rw [hSeq]; exact ⟨1, rfl⟩
        · have h2m : (2 : Fin 3) ∉ (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) :=
            fun hc => h0m (hS02.mpr hc)
          have hSeq : (Finset.univ.filter (fun k : Fin 3 => e ∈ (q k).edges)) = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨x, hx⟩
            have hs := hSsub hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hs
            rcases hs with rfl | rfl
            · exact h0m hx
            · exact h2m hx
          rw [hSeq]; exact ⟨0, rfl⟩
    obtain ⟨w, hw⟩ := lemma1 (by decide : Odd 3) q hsimple hFeven
    have hconn : Connects G s t (twoZero r₁ r₂) := by
      rw [connects_iff_exists_walk]
      refine ⟨w, fun e he => ?_⟩
      rw [twoZero_apply]
      have hne := hw e he
      push Not at hne
      exact hne
    have hval := (hImpl (twoZero r₁ r₂)).mpr hconn
    rw [thresholdFun_eq_true_iff, ones_twoZero hr12] at hval
    omega

end Network
end Switching

namespace Switching

/-- From `k ≤ 2^m` (with `k ≠ 0`) deduce `log₂ k ≤ m`. -/
theorem log2_le_of_le_pow {k m : ℕ} (hk : k ≠ 0) (h : k ≤ 2 ^ m) : Nat.log2 k ≤ m := by
  have h1 : 2 ^ Nat.log2 k ≤ k := ((Nat.log2_eq_iff hk).mp rfl).1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans h1 h)

namespace Network

variable {n : ℕ} {V E : Type} [DecidableEq E]

/-- The set of **all** switches of the variable `i` in the network. -/
def labelSet [Fintype E] (G : Network (Fin n) V E) (i : Fin n) : Finset E :=
  (Finset.univ : Finset E).filter (fun e => G.lab e = i)

theorem switchSet_subset_labelSet [Fintype E] {G : Network (Fin n) V E} {s t : V}
    (p : Walk G s t) (i : Fin n) : switchSet G p i ⊆ labelSet G i := by
  intro e he
  rw [mem_switchSet] at he
  rw [labelSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ e, he.2⟩

/-- The row diversity of the switch-set matrix is bounded by the number of
subsets of the switches of that variable. -/
theorem mu_le_two_pow [Fintype E] {G : Network (Fin n) V E} {s t : V} (p : Fin n → Walk G s t)
    (i : Fin n) :
    mu (fun i j : Fin n => switchSet G (p j) i) i ≤ 2 ^ (labelSet G i).card := by
  unfold mu
  calc ((Finset.univ : Finset (Fin n)).image (fun j => switchSet G (p j) i)).card
      ≤ ((labelSet G i).powerset).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_powerset]
        rcases Finset.mem_image.mp hw with ⟨j, -, rfl⟩
        exact switchSet_subset_labelSet (p j) i
    _ = 2 ^ (labelSet G i).card := Finset.card_powerset _

/-- The switches split the edges by their label: the total number of edges is
the sum of the numbers of switches of each variable. -/
theorem sum_card_labelSet [Fintype E] (G : Network (Fin n) V E) :
    (∑ i : Fin n, (labelSet G i).card) = Fintype.card E := by
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∀ j ∈ (Finset.univ : Finset (Fin n)), i ≠ j → Disjoint (labelSet G i) (labelSet G j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro e hi hj
    rw [labelSet, Finset.mem_filter] at hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hbU : (Finset.univ : Finset (Fin n)).biUnion (labelSet G) = Finset.univ := by
    ext e
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, -, -⟩; exact Finset.mem_univ e
    · intro _
      exact ⟨G.lab e, Finset.mem_univ _,
        by simp [labelSet]⟩
  rw [← Finset.card_univ, ← hbU, Finset.card_biUnion hdisj]

/-- **Part III of Theorem 1** (non-asymptotic form).  Any monotone 2-pole network
computing `T_{n-1}^n` whose structure is given by `n` paths avoiding the
corresponding variable has complexity at least `(n - (2k-1)!) · log₂ k`, for every
`k` with `(2k)! ≤ n`. -/
theorem complexity_lower_bound [Fintype E] {G : Network (Fin n) V E} {s t : V}
    (hn : 2 ≤ n) (hImpl : Network.Implements G s t (thresholdFun (n - 1) n))
    (p : Fin n → Walk G s t) (hacyc : ∀ i, (p i).edges.Nodup)
    (havoid : ∀ i, ∀ e ∈ (p i).edges, G.lab e ≠ i)
    (k : ℕ) (hk : 1 ≤ k) (hnk : (2 * k).factorial ≤ n) :
    (n - (2 * k - 1).factorial) * Nat.log2 k ≤ G.complexity := by
  let A : Fin n → Fin n → Finset E := fun i j => switchSet G (p j) i
  have hA : IsGood A := isGood_matrix hn hImpl p hacyc havoid
  have hcount := counting_lemma k hk A hA (by simpa using hnk)
  have hcard_eq : (Finset.univ.filter (fun i : Fin n => mu A i < k)).card
      + (Finset.univ.filter (fun i : Fin n => k ≤ mu A i)).card = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => mu A i < k)
    simpa [Fintype.card_fin, not_lt] using this
  have hbig : n - (2 * k - 1).factorial
      ≤ (Finset.univ.filter (fun i : Fin n => k ≤ mu A i)).card := by
    have hfac : (2 * k - 1).factorial ≤ (2 * k).factorial := Nat.factorial_le (by omega)
    omega
  calc (n - (2 * k - 1).factorial) * Nat.log2 k
      ≤ (Finset.univ.filter (fun i : Fin n => k ≤ mu A i)).card * Nat.log2 k :=
        Nat.mul_le_mul_right _ hbig
    _ = ∑ i ∈ (Finset.univ.filter (fun i : Fin n => k ≤ mu A i)), Nat.log2 k := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin n => k ≤ mu A i)), (labelSet G i).card := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_filter] at hi
        exact log2_le_of_le_pow (by omega) (le_trans hi.2 (mu_le_two_pow p i))
    _ ≤ ∑ i : Fin n, (labelSet G i).card := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i; exact Nat.zero_le _
    _ = Fintype.card E := sum_card_labelSet G
    _ = G.complexity := rfl

end Network
end Switching

namespace Switching

/-- **Theorem 1** of Sergeev, in non-asymptotic form, stated for an *arbitrary*
monotone 2-pole network (no structural hypothesis).

Let `G` be a monotone 2-pole network on `n ≥ 2` variables that computes the
threshold function `T_{n-1}^n`.  Then for every `k` with `(2k)! ≤ n`,

  `(n - (2k-1)!) · log₂ k ≤ #switches`.

The paper's reduction "the minimal network is a union of `n`
paths `p i` avoiding the variable `x_i`" is *derived* here, following the three
steps of the proof strategy.

* Point (1), `x_i`-free walks exist.  For each `i` the assignment `singleZero i`
  (the only false coordinate is `i`) has `n - 1` true coordinates, so it
  satisfies `T_{n-1}^n`.  Since `G` computes `T_{n-1}^n`, its poles are connected
  using only edges labelled `≠ i`; equivalently, an `x_i`-free walk must exist,
  for if it did not then `G` would take the wrong value on `singleZero i`.

* Point (3), acyclic reduction.  Applying `Walk.exists_nodup_edges`, that
  `x_i`-free walk is replaced by an acyclic one, still `x_i`-free (the reduction
  only removes edges).  This is exactly the fact that the connectivity function
  is determined by its acyclic walks.

* Point (2), deleting unused edges, is *not* needed for this lower bound.  The
  counting argument of `Network.complexity_lower_bound` bounds the number of
  switches below by the total number of edges of `G` (via the partition of the
  edges by label), so additional edges only relax the inequality.  Thus the bound
  holds for every network computing `T_{n-1}^n`, minimal or not.

Choosing `k ≈ log n / log log n` (the paper's part III) yields the stated
asymptotic lower bound `K⁺(T_{n-1}^n) ⪰ n log log n`. -/
theorem theorem1 {n : ℕ} (hn : 2 ≤ n) {V E : Type} [DecidableEq E] [Fintype E]
    {G : Network (Fin n) V E} {s t : V}
    (hImpl : Network.Implements G s t (thresholdFun (n - 1) n))
    (k : ℕ) (hk : 1 ≤ k) (hnk : (2 * k).factorial ≤ n) :
    (n - (2 * k - 1).factorial) * Nat.log2 k ≤ G.complexity := by
  -- Point (1): for each `i` there is an `x_i`-free walk from `s` to `t`.
  have hwalk : ∀ i : Fin n, ∃ W : Network.Walk G s t,
      W.edges.Nodup ∧ ∀ e ∈ W.edges, G.lab e ≠ i := by
    intro i
    have hone : ones (singleZero i) = n - 1 := ones_singleZero i
    have ht : thresholdFun (n - 1) n (singleZero i) = true := by
      rw [thresholdFun_eq_true_iff, hone]
    have hconn : Network.Connects G s t (singleZero i) := (hImpl (singleZero i)).mp ht
    obtain ⟨W, hW⟩ := hconn
    have hP : ∀ e ∈ W.edges, G.lab e ≠ i := by
      rw [Network.Walk.eval_eq_true_iff] at hW
      intro e he
      have := hW e he
      simpa [singleZero] using this
    -- Point (3): reduce the walk to an acyclic one with the same property.
    exact Network.Walk.exists_nodup_edges W _ hP
  let p : Fin n → Network.Walk G s t := fun i => (hwalk i).choose
  have hpN : ∀ i, (p i).edges.Nodup := fun i => (hwalk i).choose_spec.1
  have hpA : ∀ i, ∀ e ∈ (p i).edges, G.lab e ≠ i := fun i => (hwalk i).choose_spec.2
  exact Network.complexity_lower_bound hn hImpl p hpN hpA k hk hnk

/-- **Theorem 1** of Sergeev as a genuine lower bound on the switching complexity:
for every `n ≥ 2` and every `k` with `(2k)! ≤ n`, the switching complexity of the
threshold function `T_{n-1}^n` (the infimum of the number of switches over all
monotone 2-pole networks computing it — the quantity `K⁺(T_{n-1}^n)` of the paper)
is at least `(n - (2k-1)!) · log₂ k`.

This is obtained by applying `theorem1` to *every* network implementing
`T_{n-1}^n` appearing in the infimum defining `switchingComplexity`. -/
theorem switchingComplexity_threshold_ge {n : ℕ} (hn : 2 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hnk : (2 * k).factorial ≤ n) :
    (((n - (2 * k - 1).factorial) * Nat.log2 k : ℕ) : ℕ∞)
      ≤ switchingComplexity (thresholdFun (n - 1) n) := by
  unfold switchingComplexity
  refine le_sInf ?_
  rintro c ⟨_, m, N, hN, rfl⟩
  have hm : (n - (2 * k - 1).factorial) * Nat.log2 k ≤ m := by
    simpa only [Network.complexity, Fintype.card_fin] using
      theorem1 hn (G := N.toNetwork) (s := N.s) (t := N.t) hN k hk hnk
  exact_mod_cast hm

end Switching


/-!
# Sanity checks for the switching-network formalization

This file collects a couple of elementary facts and worked examples that exercise
the definitions in `ContactThresh.Switching` and the proofs in
`ContactThresh.Proofs`.
-/

namespace Switching

namespace Network

variable {α V E : Type}

/-- A walk whose two endpoints are distinct must start with an edge (it cannot be
the trivial walk). -/
theorem Walk.exists_cons_of_ne {G : Network α V E} {s t : V} (p : Walk G s t)
    (h : s ≠ t) :
    ∃ (v : V) (e : E)
      (hh : (G.src e = s ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = s))
      (q : Walk G v t), p = Walk.cons e hh q := by
  cases p with
  | nil u => exact absurd rfl h
  | cons e hh q => exact ⟨_, e, hh, q, rfl⟩

end Network

namespace Example

open Network

/-- The 2-pole network consisting of a single edge labelled `a` joining the two
poles `0` and `1`. -/
def singlePole {α : Type} (a : α) : TwoPole α (Fin 2) (Fin 1) where
  src := fun _ => 0
  tgt := fun _ => 1
  lab := fun _ => a
  s := 0
  t := 1
  hst := by decide

/-- The single-edge network between two distinct poles implements the function
`x ↦ x a`: the connectivity function of its unique path is the product of the
labels of that path, i.e. the variable `a` itself. -/
theorem singlePole_implements {α : Type} (a : α) :
    (singlePole a).Implements (fun x => x a) := by
  intro x
  constructor
  · intro hx
    refine ⟨Walk.cons (G := (singlePole a).toNetwork) 0 (by left; exact ⟨rfl, rfl⟩)
      (Walk.nil 1), ?_⟩
    rw [Walk.eval_eq_true_iff]
    intro e _
    simpa [singlePole] using hx
  · rintro ⟨p, hp⟩
    obtain ⟨v, e, hh, q, rfl⟩ := p.exists_cons_of_ne (by decide : (0 : Fin 2) ≠ 1)
    rw [Walk.eval_eq_true_iff] at hp
    have := hp e (by simp [Walk.edges])
    simpa [singlePole] using this

/-- The single-edge network has complexity one. -/
example {α : Type} (a : α) : (singlePole a).complexity = 1 := by
  simp [TwoPole.complexity, Network.complexity]

/-- Consequently, the switching complexity of `x ↦ x a` is at most one. -/
example {α : Type} (a : α) :
    switchingComplexity (fun x : α → Bool => x a) ≤ (1 : ℕ∞) :=
  switchingComplexity_le (singlePole_implements a)

/-! ## A sanity check for Lemma 1 -/

/-- A network with two parallel edges joining the two poles `0` and `1`. -/
abbrev parallel : Network Unit (Fin 2) (Fin 2) where
  src := fun _ => 0
  tgt := fun _ => 1
  lab := fun _ => ()

/-- The walk consisting of the single edge `e` joining the poles. -/
def singleEdge (e : Fin 2) : Walk parallel 0 1 :=
  .cons e (Or.inl ⟨rfl, rfl⟩) (.nil 1)

/-- Sanity check for `lemma1`.  The three acyclic paths `e₀, e₀, e₁` join the
poles; edge `0` lies on an even number (two) of them and `m = 3` is odd, so the
lemma guarantees that the poles stay connected without edge `0` — namely via
edge `1`. -/
example : ConnectsAvoiding parallel (fun e => e = 0) 0 1 := by
  refine lemma1 (by decide : Odd 3)
    (fun i : Fin 3 => if i = 2 then singleEdge 1 else singleEdge 0) ?_ ?_
  · intro i; fin_cases i <;> decide
  · intro e he
    fin_cases e
    · decide
    · simp at he

end Example

namespace Example

open Network

/-! ## A sanity check for Theorem 1 -/

/-- The 2-pole monotone network with two parallel edges labelled `0` and `1`
joining the poles `0` and `1`. -/
def orNet : Network (Fin 2) (Fin 2) (Fin 2) where
  src := fun _ => 0
  tgt := fun _ => 1
  lab := fun e => e

/-- `1 ≤ ones x` holds exactly when `x` is true at some coordinate. -/
theorem one_le_ones_iff {n : ℕ} {x : Fin n → Bool} : 1 ≤ ones x ↔ ∃ i, x i = true := by
  rw [ones, Finset.one_le_card]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, (Finset.mem_filter.mp hi).2⟩,
    fun ⟨i, hi⟩ => ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩⟩

/-- The walk that traverses the single edge `e` from the pole `0` to the pole `1`. -/
def edgeWalk (e : Fin 2) : Walk orNet 0 1 :=
  .cons e (Or.inl ⟨rfl, rfl⟩) (.nil 1)

/-- `orNet` computes `T_1^2`, i.e. the disjunction `x 0 ∨ x 1 = x 0 ∨ x 1`.  In
particular the hypotheses of `theorem1` are satisfiable, so the restated Theorem 1
is not vacuous. -/
theorem orNet_implements : orNet.Implements 0 1 (thresholdFun 1 2) := by
  intro x
  rw [thresholdFun_eq_true_iff, one_le_ones_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨edgeWalk i, (Walk.eval_eq_true_iff _ x).mpr (fun e he => by
      simp only [edgeWalk, Walk.edges, List.mem_singleton] at he
      subst he
      simpa [orNet] using hi)⟩
  · rintro ⟨W, hW⟩
    obtain ⟨v, e, hh, q, rfl⟩ := W.exists_cons_of_ne (by decide : (0 : Fin 2) ≠ 1)
    rw [Walk.eval_eq_true_iff] at hW
    exact ⟨orNet.lab e, hW e (by simp [Walk.edges])⟩

/-- `theorem1` instantiates on `orNet` given only the implementation hypothesis
(no assumption on the network's structure). -/
example : (2 - (2 * 1 - 1).factorial) * Nat.log2 1 ≤ orNet.complexity :=
  theorem1 (by decide : 2 ≤ 2) (s := 0) (t := 1) orNet_implements 1 le_rfl (by decide)

end Example

end Switching
