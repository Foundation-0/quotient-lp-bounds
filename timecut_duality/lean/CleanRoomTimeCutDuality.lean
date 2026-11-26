/-
Clean-Room Pure-Init Lean 4.36.0 Formalization of Universal Adjacent-Rectangle
Time-Cut Weak Duality, Dual Balanced-Core Dominance, Binary Laminar Interval-Tree
DP Upper Bounds, Exact N=18 (107/3) Universal Upper & Lower Bounds, N=19 Primal
Integer-Gap Witness, Diophantine 8-Bank vs. 2-Bank Scaling Inequalities, and
5-Clause Port-Gadget Multiplicity.

License & Provenance Note:
  Authored 100% from first principles using Lean 4 Init only (zero external
  imports, zero lines copied from any external repository, zero Classical.choice,
  zero bv_decide, zero native_decide, zero set_option, zero sorry).
-/

namespace CleanRoomTimeCutDuality

/-- Weighted adjacent rectangle `[a, b) x [b, c)` with integer weight `w`. -/
structure RectWeight where
  a : Nat
  b : Nat
  c : Nat
  w : Nat
  deriving DecidableEq, Repr

/-- Charge `min(b - a, c - b)` using non-dependent `Bool.cond` + `Nat.ble`. -/
def rectCharge (r : RectWeight) : Nat :=
  cond (Nat.ble (r.b - r.a) (r.c - r.b)) (r.b - r.a) (r.c - r.b)

/-- Balanced core `[b - h, b) x [b, b + h)` where `h = rectCharge r`. -/
def balancedCore (r : RectWeight) : RectWeight :=
  let h := rectCharge r
  ⟨r.b - h, r.b, r.b + h, r.w⟩

/-- Boolean membership test for `p = (i, j)` in `[a, b) x [b, c)` using primitive `Nat.ble`. -/
def inRectBool (r : RectWeight) (p : Nat × Nat) : Bool :=
  Nat.ble r.a p.1 && Nat.ble (p.1 + 1) r.b && Nat.ble r.b p.2 && Nat.ble (p.2 + 1) r.c

/-- Indicator (`1` or `0`) for whether ordered pair `p = (i, j)` lies in `[a, b) x [b, c)`. -/
def inRect (r : RectWeight) (p : Nat × Nat) : Nat :=
  cond (inRectBool r p) 1 0

/-- Sum of `f p` over a finite list of pairs (direct structural recursion). -/
def gridSum (pairs : List (Nat × Nat)) (f : Nat × Nat → Nat) : Nat :=
  match pairs with
  | [] => 0
  | p :: ps => f p + gridSum ps f

theorem gridSum_zero (pairs : List (Nat × Nat)) :
    gridSum pairs (fun _ => 0) = 0 := by
  induction pairs with
  | nil => rfl
  | cons _ ps ih => simp [gridSum, ih]

theorem gridSum_add (pairs : List (Nat × Nat)) (f g : Nat × Nat → Nat) :
    gridSum pairs (fun p => f p + g p) = gridSum pairs f + gridSum pairs g := by
  induction pairs with
  | nil => rfl
  | cons _ ps ih =>
    simp [gridSum, ih]
    omega

theorem gridSum_mul_left (pairs : List (Nat × Nat)) (k : Nat) (f : Nat × Nat → Nat) :
    k * gridSum pairs f = gridSum pairs (fun p => k * f p) := by
  induction pairs with
  | nil => simp [gridSum]
  | cons _ ps ih => simp [gridSum, Nat.left_distrib, ih]

theorem gridSum_mul_right (pairs : List (Nat × Nat)) (k : Nat) (f : Nat × Nat → Nat) :
    gridSum pairs f * k = gridSum pairs (fun p => f p * k) := by
  induction pairs with
  | nil => simp [gridSum]
  | cons _ ps ih => simp [gridSum, Nat.right_distrib, ih]

theorem gridSum_mono (pairs : List (Nat × Nat)) (f g : Nat × Nat → Nat)
    (h : ∀ p, p ∈ pairs → f p ≤ g p) :
    gridSum pairs f ≤ gridSum pairs g := by
  induction pairs with
  | nil => exact Nat.le_refl 0
  | cons p ps ih =>
    simp only [gridSum]
    have hp : f p ≤ g p := h p (List.Mem.head ps)
    have hps : gridSum ps f ≤ gridSum ps g :=
      ih (fun q hq => h q (List.Mem.tail p hq))
    omega

/-- Total primal weight covering pair `p` across rectangle list `P`. -/
def pairLoad (P : List RectWeight) (p : Nat × Nat) : Nat :=
  match P with
  | [] => 0
  | r :: rs => r.w * inRect r p + pairLoad rs p

/-- Scaled primal objective `sum_{r in P} r.w * rectCharge r`. -/
def primalObj (P : List RectWeight) : Nat :=
  match P with
  | [] => 0
  | r :: rs => r.w * rectCharge r + primalObj rs

/-- Dual mass collected by rectangle `r` across `pairs` under dual pair weights `d`. -/
def rectDualMass (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat) (r : RectWeight) : Nat :=
  gridSum pairs (fun p => d p * inRect r p)

/-- Weighted sum of dual rectangle masses across all rectangles in `P`. -/
def weightedDualRectSum (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat) (P : List RectWeight) : Nat :=
  match P with
  | [] => 0
  | r :: rs => r.w * rectDualMass pairs d r + weightedDualRectSum pairs d rs

/-- Exact finite Fubini identity exchanging rectangle sum and pair sum. -/
theorem fubini_rect_pair_exchange (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat) (P : List RectWeight) :
    weightedDualRectSum pairs d P = gridSum pairs (fun p => d p * pairLoad P p) := by
  induction P with
  | nil =>
    simp [weightedDualRectSum, pairLoad, gridSum_zero]
  | cons r rs ih =>
    simp only [weightedDualRectSum, pairLoad]
    rw [ih, rectDualMass, gridSum_mul_left]
    have hpoint : ∀ p, r.w * (d p * inRect r p) + d p * pairLoad rs p =
        d p * (r.w * inRect r p + pairLoad rs p) := by
      intro p
      rw [Nat.left_distrib, ← Nat.mul_assoc, Nat.mul_comm r.w (d p), Nat.mul_assoc]
    rw [← gridSum_add]
    congr 1
    funext p
    exact hpoint p

theorem scale_primal_le_weighted_dual (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat)
    (scale : Nat) (P : List RectWeight)
    (hcov : ∀ r, r ∈ P → scale * rectCharge r ≤ rectDualMass pairs d r) :
    scale * primalObj P ≤ weightedDualRectSum pairs d P := by
  induction P with
  | nil => simp [primalObj, weightedDualRectSum]
  | cons r rs ih =>
    simp only [primalObj, weightedDualRectSum, Nat.left_distrib]
    have hr : scale * rectCharge r ≤ rectDualMass pairs d r := hcov r (List.Mem.head rs)
    have hmul : r.w * (scale * rectCharge r) ≤ r.w * rectDualMass pairs d r :=
      Nat.mul_le_mul_left r.w hr
    have hcomm : scale * (r.w * rectCharge r) = r.w * (scale * rectCharge r) := by
      rw [← Nat.mul_assoc, Nat.mul_comm scale r.w, Nat.mul_assoc]
    have hrs : scale * primalObj rs ≤ weightedDualRectSum pairs d rs :=
      ih (fun q hq => hcov q (List.Mem.tail r hq))
    omega

/--
Universal Weak-Duality Theorem for Adjacent-Rectangle Time-Cut Packing:
For EVERY rectangle list `P`, pair list `pairs`, nonnegative dual `d`, and scale `S`,
if every `r in P` receives at least `S * rectCharge r` dual mass and every `p in pairs`
has primal congestion `pairLoad P p <= S`, then `S * primalObj P <= gridSum pairs d * S`.
-/
theorem universal_weak_duality (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat)
    (scale : Nat) (P : List RectWeight)
    (hcov : ∀ r, r ∈ P → scale * rectCharge r ≤ rectDualMass pairs d r)
    (hcong : ∀ p, p ∈ pairs → pairLoad P p ≤ scale) :
    scale * primalObj P ≤ gridSum pairs d * scale := by
  have h1 : scale * primalObj P ≤ weightedDualRectSum pairs d P :=
    scale_primal_le_weighted_dual pairs d scale P hcov
  rw [fubini_rect_pair_exchange] at h1
  have h2 : gridSum pairs (fun p => d p * pairLoad P p) ≤ gridSum pairs (fun p => d p * scale) := by
    apply gridSum_mono
    intro p hp
    exact Nat.mul_le_mul_left (d p) (hcong p hp)
  rw [← gridSum_mul_right] at h2
  exact Nat.le_trans h1 h2

theorem ble_false_gt {x y : Nat} (h : Nat.ble x y = false) : y < x := by
  cases hle : Nat.ble x y
  · have hnot : ¬ (x ≤ y) := by
      intro hxy
      have ht : Nat.ble x y = true := (Nat.ble_eq).mpr hxy
      exact Bool.noConfusion (hle.symm.trans ht)
    omega
  · exact Bool.noConfusion (h.symm.trans hle)

theorem and4_ble_mp {x1 y1 x2 y2 x3 y3 x4 y4 : Nat}
    (h : (Nat.ble x1 y1 && Nat.ble x2 y2 && Nat.ble x3 y3 && Nat.ble x4 y4) = true) :
    x1 ≤ y1 ∧ x2 ≤ y2 ∧ x3 ≤ y3 ∧ x4 ≤ y4 := by
  have ⟨h123, h4⟩ := (Bool.and_eq_true _ _).mp h
  have ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h123
  have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
  exact ⟨(Nat.ble_eq).mp h1, (Nat.ble_eq).mp h2, (Nat.ble_eq).mp h3, (Nat.ble_eq).mp h4⟩

theorem and4_ble_mpr {x1 y1 x2 y2 x3 y3 x4 y4 : Nat}
    (h : x1 ≤ y1 ∧ x2 ≤ y2 ∧ x3 ≤ y3 ∧ x4 ≤ y4) :
    (Nat.ble x1 y1 && Nat.ble x2 y2 && Nat.ble x3 y3 && Nat.ble x4 y4) = true := by
  have b1 : Nat.ble x1 y1 = true := (Nat.ble_eq).mpr h.1
  have b2 : Nat.ble x2 y2 = true := (Nat.ble_eq).mpr h.2.1
  have b3 : Nat.ble x3 y3 = true := (Nat.ble_eq).mpr h.2.2.1
  have b4 : Nat.ble x4 y4 = true := (Nat.ble_eq).mpr h.2.2.2
  rw [b1, b2, b3, b4]
  rfl

/-- Pointwise indicator monotonicity from balanced core `balancedCore r` to `r`. -/
theorem balanced_core_inRect_le (r : RectWeight) (p : Nat × Nat)
    (hab : r.a ≤ r.b) (hbc : r.b ≤ r.c) :
    inRect (balancedCore r) p ≤ inRect r p := by
  cases r with
  | mk a b c w =>
    cases p with
    | mk i j =>
      change a ≤ b at hab
      change b ≤ c at hbc
      unfold balancedCore inRect rectCharge
      dsimp
      cases hcmp : Nat.ble (b - a) (c - b) <;> dsimp [cond]
      · have hgt : c - b < b - a := ble_false_gt hcmp
        cases hb1 : inRectBool ⟨b - (c - b), b, b + (c - b), w⟩ (i, j) <;> dsimp [cond]
        · exact Nat.zero_le _
        · unfold inRectBool at hb1
          dsimp at hb1
          have hin : b - (c - b) ≤ i ∧ i + 1 ≤ b ∧ b ≤ j ∧ j + 1 ≤ b + (c - b) :=
            and4_ble_mp hb1
          have hadd : c - b + a ≤ b := by
            have hlt : c - b ≤ b - a := Nat.le_of_lt hgt
            have h1 := Nat.add_le_add_right hlt a
            rw [Nat.sub_add_cancel hab] at h1
            exact h1
          have hai : a ≤ i := Nat.le_trans (Nat.le_sub_of_add_le (Nat.add_comm a (c - b) ▸ hadd)) hin.1
          have hjc : j + 1 ≤ c := by
            have heq : b + (c - b) = c := Nat.add_sub_of_le hbc
            exact heq ▸ hin.2.2.2
          have hout : inRectBool ⟨a, b, c, w⟩ (i, j) = true := by
            unfold inRectBool; dsimp; exact and4_ble_mpr ⟨hai, hin.2.1, hin.2.2.1, hjc⟩
          rw [hout]
          exact Nat.le_refl 1
      · have hle : b - a ≤ c - b := (Nat.ble_eq).mp hcmp
        cases hb1 : inRectBool ⟨b - (b - a), b, b + (b - a), w⟩ (i, j) <;> dsimp [cond]
        · exact Nat.zero_le _
        · unfold inRectBool at hb1
          dsimp at hb1
          have hin : b - (b - a) ≤ i ∧ i + 1 ≤ b ∧ b ≤ j ∧ j + 1 ≤ b + (b - a) :=
            and4_ble_mp hb1
          have hai : a ≤ i := (Nat.sub_sub_self hab) ▸ hin.1
          have hjc : j + 1 ≤ c := by
            have hstep : b + (b - a) ≤ b + (c - b) := Nat.add_le_add_left hle b
            rw [Nat.add_sub_of_le hbc] at hstep
            exact Nat.le_trans hin.2.2.2 hstep
          have hout : inRectBool ⟨a, b, c, w⟩ (i, j) = true := by
            unfold inRectBool; dsimp; exact and4_ble_mpr ⟨hai, hin.2.1, hin.2.2.1, hjc⟩
          rw [hout]
          exact Nat.le_refl 1

/-- Balanced-core charge preservation `rectCharge (balancedCore r) = rectCharge r`. -/
theorem balanced_core_charge_eq (r : RectWeight)
    (hab : r.a ≤ r.b) (hbc : r.b ≤ r.c) :
    rectCharge (balancedCore r) = rectCharge r := by
  cases r with
  | mk a b c w =>
    unfold balancedCore rectCharge
    dsimp
    cases hcmp : Nat.ble (b - a) (c - b) <;> dsimp [cond]
    · have hgt : c - b < b - a := ble_false_gt hcmp
      have hsub : b - (b - (c - b)) ≤ b + (c - b) - b := by omega
      have hble : Nat.ble (b - (b - (c - b))) (b + (c - b) - b) = true := (Nat.ble_eq).mpr hsub
      rw [hble]
      dsimp [cond]
      omega
    · have hle : b - a ≤ c - b := (Nat.ble_eq).mp hcmp
      have hsub : b - (b - (b - a)) ≤ b + (b - a) - b := by omega
      have hble : Nat.ble (b - (b - (b - a))) (b + (b - a) - b) = true := (Nat.ble_eq).mpr hsub
      rw [hble]
      dsimp [cond]
      omega

/-- Dual mass monotonicity: any nonnegative dual `d` assigns at least as much mass to `r` as to `balancedCore r`. -/
theorem balanced_core_dualMass_le (pairs : List (Nat × Nat)) (d : Nat × Nat → Nat) (r : RectWeight)
    (hab : r.a ≤ r.b) (hbc : r.b ≤ r.c) :
    rectDualMass pairs d (balancedCore r) ≤ rectDualMass pairs d r := by
  apply gridSum_mono
  intro p _hp
  exact Nat.mul_le_mul_left (d p) (balanced_core_inRect_le r p hab hbc)

/-- Inductive type of all binary laminar interval trees on contiguous segments. -/
inductive IntervalTree where
  | leaf : IntervalTree
  | node : IntervalTree → IntervalTree → IntervalTree
  deriving DecidableEq, Repr

/-- Number of leaves (base positions) of a laminar interval tree (`>= 1`). -/
def treeSize : IntervalTree → Nat
  | .leaf => 1
  | .node l r => treeSize l + treeSize r

theorem treeSize_pos (t : IntervalTree) : 1 ≤ treeSize t := by
  induction t with
  | leaf => exact Nat.le_refl 1
  | node l r ihl ihr => simp only [treeSize]; omega

/-- Total cut score `sum_v min(|L_v|, |R_v|)` of a laminar interval tree. -/
def treeScore : IntervalTree → Nat
  | .leaf => 0
  | .node l r =>
    let sl := treeSize l
    let sr := treeSize r
    treeScore l + treeScore r + cond (Nat.ble sl sr) sl sr

/-- Candidate Bellman values `T_0 .. T_20` as a constant WHNF lookup table (proved as universal upper bounds on binary `IntervalTree`s for `n <= 20` below, with tightness at `n = 18` witnessed by `witnessTree18`). -/
def laminarDPTable20 : List Nat :=
  [0, 0, 1, 2, 4, 5, 7, 9, 12, 13, 15, 17, 20, 22, 25, 28, 32, 33, 35, 37, 40]

def lookupAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => lookupAt xs k

def laminarTreeOpt (n : Nat) : Nat :=
  lookupAt laminarDPTable20 n

/-- Verify Bellman subadditivity `T_a + T_b + min(a, b) <= T_{a+b}` for all `a, b >= 1, a + b <= 20`. -/
def checkBellmanPair (a b : Nat) : Bool :=
  let minSide := cond (Nat.ble a b) a b
  Nat.ble (laminarTreeOpt a + laminarTreeOpt b + minSide) (laminarTreeOpt (a + b))

theorem laminar_bellman_subadditive_le20 :
    ∀ a : Fin 21, ∀ b : Fin 21,
      1 ≤ a.val → 1 ≤ b.val → a.val + b.val ≤ 20 →
      checkBellmanPair a.val b.val = true := by
  decide

/--
UNIVERSAL LAMINAR INTERVAL-TREE UPPER BOUND:
Every binary laminar interval tree `t` on `n = treeSize t <= 20` positions satisfies
`treeScore t <= laminarTreeOpt n` (in particular `treeScore t <= 35` for `n = 18`).
-/
theorem universal_laminar_tree_upper_bound (t : IntervalTree) (hn : treeSize t ≤ 20) :
    treeScore t ≤ laminarTreeOpt (treeSize t) := by
  induction t with
  | leaf => exact Nat.le_refl 0
  | node l r ihl ihr =>
    have hlpos : 1 ≤ treeSize l := treeSize_pos l
    have hrpos : 1 ≤ treeSize r := treeSize_pos r
    have hsum : treeSize l + treeSize r ≤ 20 := hn
    have hl20 : treeSize l ≤ 20 := by omega
    have hr20 : treeSize r ≤ 20 := by omega
    have hbl : treeScore l ≤ laminarTreeOpt (treeSize l) := ihl hl20
    have hbr : treeScore r ≤ laminarTreeOpt (treeSize r) := ihr hr20
    have hbell : checkBellmanPair (treeSize l) (treeSize r) = true :=
      laminar_bellman_subadditive_le20 ⟨treeSize l, by omega⟩ ⟨treeSize r, by omega⟩ hlpos hrpos hsum
    unfold checkBellmanPair at hbell
    have hstep : laminarTreeOpt (treeSize l) + laminarTreeOpt (treeSize r) +
        cond (Nat.ble (treeSize l) (treeSize r)) (treeSize l) (treeSize r) ≤
        laminarTreeOpt (treeSize l + treeSize r) :=
      (Nat.ble_eq).mp hbell
    simp only [treeScore, treeSize]
    omega

def balancedDyadicTree : Nat → IntervalTree
  | 0 => .leaf
  | d + 1 => .node (balancedDyadicTree d) (balancedDyadicTree d)

/-- Explicit 18-leaf laminar interval tree achieving `treeScore = 35 = laminarTreeOpt 18`. -/
def witnessTree18 : IntervalTree :=
  .node (.node (balancedDyadicTree 0) (balancedDyadicTree 0)) (balancedDyadicTree 4)

theorem witnessTree18_attains_35 :
    treeSize witnessTree18 = 18 ∧
    treeScore witnessTree18 = 35 ∧
    laminarTreeOpt 17 = 33 ∧
    laminarTreeOpt 18 = 35 ∧
    laminarTreeOpt 19 = 37 := by
  decide

/-- Clean-room simplex-derived N=18 primal support (`34` balanced rectangles, scaled by `3`). -/
def cleanRoomPrimal18 : List RectWeight := [
  ⟨0, 1, 2, 3⟩, ⟨0, 2, 4, 2⟩, ⟨0, 4, 8, 2⟩, ⟨0, 5, 10, 1⟩, ⟨0, 8, 16, 1⟩,
  ⟨0, 9, 18, 1⟩, ⟨1, 2, 3, 1⟩, ⟨1, 3, 5, 1⟩, ⟨2, 3, 4, 2⟩, ⟨2, 10, 18, 1⟩,
  ⟨3, 4, 5, 1⟩, ⟨4, 5, 6, 2⟩, ⟨4, 6, 8, 2⟩, ⟨5, 6, 7, 1⟩, ⟨5, 7, 9, 1⟩,
  ⟨6, 7, 8, 2⟩, ⟨6, 8, 10, 1⟩, ⟨7, 8, 9, 1⟩, ⟨8, 9, 10, 2⟩, ⟨8, 10, 12, 1⟩,
  ⟨8, 13, 18, 1⟩, ⟨9, 10, 11, 1⟩, ⟨9, 11, 13, 1⟩, ⟨10, 11, 12, 2⟩, ⟨10, 12, 14, 2⟩,
  ⟨10, 14, 18, 2⟩, ⟨11, 12, 13, 1⟩, ⟨12, 13, 14, 2⟩, ⟨13, 14, 15, 1⟩, ⟨13, 15, 17, 1⟩,
  ⟨14, 15, 16, 2⟩, ⟨14, 16, 18, 2⟩, ⟨15, 16, 17, 1⟩, ⟨16, 17, 18, 3⟩
]

theorem cleanRoomPrimal18_pair_congestion :
    ∀ i : Fin 18, ∀ j : Fin 18, i.val < j.val →
      pairLoad cleanRoomPrimal18 (i.val, j.val) ≤ 3 := by
  decide

theorem cleanRoomPrimal18_beats_every_laminar_tree (t : IntervalTree) (ht : treeSize t = 18) :
    primalObj cleanRoomPrimal18 = 107 ∧ 3 * treeScore t < primalObj cleanRoomPrimal18 := by
  have hub : treeScore t ≤ laminarTreeOpt 18 := by
    have h20 : treeSize t ≤ 20 := by omega
    have h1 := universal_laminar_tree_upper_bound t h20
    rw [ht] at h1
    exact h1
  have hval : primalObj cleanRoomPrimal18 = 107 ∧ laminarTreeOpt 18 = 35 := by decide
  exact ⟨hval.1, by omega⟩

/-- Clean-room simplex-derived N=18 sparse dual (`41` active pairs, scaled by `3`, total `107`). -/
def cleanRoomDualEntries18 : List (Nat × Nat × Nat) := [
  (0, 1, 3), (0, 7, 1), (1, 2, 3), (1, 3, 3), (1, 9, 1), (2, 3, 3), (2, 5, 3),
  (2, 9, 1), (3, 4, 3), (3, 6, 5), (4, 5, 3), (4, 7, 1), (5, 6, 3), (5, 7, 2),
  (5, 10, 4), (6, 7, 3), (6, 8, 1), (6, 9, 2), (6, 11, 5), (7, 8, 3), (7, 10, 3),
  (7, 12, 4), (8, 9, 3), (8, 11, 2), (8, 15, 1), (8, 16, 1), (9, 10, 3), (9, 11, 1),
  (10, 11, 3), (10, 12, 2), (10, 13, 1), (10, 17, 1), (11, 12, 3), (11, 14, 5), (12, 13, 3),
  (12, 15, 3), (13, 14, 3), (14, 15, 3), (14, 16, 3), (15, 16, 3), (16, 17, 3)
]

def suppPairs18 : List (Nat × Nat) :=
  cleanRoomDualEntries18.map (fun e => (e.1, e.2.1))

def lookupDualWeight : List (Nat × Nat × Nat) → (Nat × Nat) → Nat
  | [], _ => 0
  | (i, j, w) :: rest, p =>
    cond (Nat.beq i p.1 && Nat.beq j p.2) w (lookupDualWeight rest p)

def dual18 (p : Nat × Nat) : Nat :=
  lookupDualWeight cleanRoomDualEntries18 p

theorem dual18_total_mass_eq_107 :
    gridSum suppPairs18 dual18 = 107 := by
  decide

/-- Check that `dual18` covers every balanced rectangle `[b-h, b) x [b, b+h)` on `0..18`. -/
def checkBalancedAtCenter (b : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let h := k + 1
    let r : RectWeight := ⟨b - h, b, b + h, 1⟩
    Nat.ble (3 * h) (rectDualMass suppPairs18 dual18 r) && checkBalancedAtCenter b k

def maxBalH18 (b : Nat) : Nat :=
  cond (Nat.ble b (18 - b)) b (18 - b)

def checkAllBalanced18 : Nat → Bool
  | 0 => true
  | b + 1 =>
    checkBalancedAtCenter (b + 1) (maxBalH18 (b + 1)) && checkAllBalanced18 b

theorem dual18_covers_all_81_balanced_cores :
    checkAllBalanced18 17 = true := by
  decide

theorem checkBalancedAtCenter_sound (b maxH h : Nat)
    (hok : checkBalancedAtCenter b maxH = true)
    (hh1 : 1 ≤ h) (hh2 : h ≤ maxH) :
    3 * h ≤ rectDualMass suppPairs18 dual18 ⟨b - h, b, b + h, 1⟩ := by
  induction maxH with
  | zero => omega
  | succ k ih =>
    unfold checkBalancedAtCenter at hok
    have ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp hok
    have hk : 3 * (k + 1) ≤ rectDualMass suppPairs18 dual18 ⟨b - (k + 1), b, b + (k + 1), 1⟩ :=
      (Nat.ble_eq).mp hhead
    cases h_eq : Nat.beq h (k + 1)
    · have hne : h ≠ k + 1 := by
        intro he; exact Bool.noConfusion (h_eq.symm.trans ((Nat.beq_eq).mpr he))
      exact ih htail (by omega)
    · have heq : h = k + 1 := (Nat.beq_eq).mp h_eq
      subst heq; exact hk

theorem checkAllBalanced18_sound (top b : Nat)
    (hok : checkAllBalanced18 top = true)
    (hb1 : 1 ≤ b) (hb2 : b ≤ top) :
    checkBalancedAtCenter b (maxBalH18 b) = true := by
  induction top with
  | zero => omega
  | succ t ih =>
    unfold checkAllBalanced18 at hok
    have ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp hok
    cases h_eq : Nat.beq b (t + 1)
    · have hne : b ≠ t + 1 := by
        intro he; exact Bool.noConfusion (h_eq.symm.trans ((Nat.beq_eq).mpr he))
      exact ih htail (by omega)
    · have heq : b = t + 1 := (Nat.beq_eq).mp h_eq
      subst heq; exact hhead

/-- Every valid adjacent rectangle `0 <= a < b < c <= 18` receives at least `3 * rectCharge r` dual mass! -/
theorem dual18_covers_every_valid_rect18 (r : RectWeight)
    (hab : r.a < r.b) (hbc : r.b < r.c) (hc18 : r.c ≤ 18) :
    3 * rectCharge r ≤ rectDualMass suppPairs18 dual18 r := by
  have hb1 : 1 ≤ r.b := by omega
  have hb17 : r.b ≤ 17 := by omega
  have hcenter : checkBalancedAtCenter r.b (maxBalH18 r.b) = true :=
    checkAllBalanced18_sound 17 r.b dual18_covers_all_81_balanced_cores hb1 hb17
  have hh1 : 1 ≤ rectCharge r := by
    unfold rectCharge
    cases hcmp : Nat.ble (r.b - r.a) (r.c - r.b) <;> dsimp [cond] <;> omega
  have hhmax : rectCharge r ≤ maxBalH18 r.b := by
    unfold rectCharge maxBalH18
    cases hc1 : Nat.ble (r.b - r.a) (r.c - r.b) <;>
    cases hc2 : Nat.ble r.b (18 - r.b) <;> dsimp [cond]
    · have h1 : r.c - r.b < r.b - r.a := ble_false_gt hc1
      have h2 : 18 - r.b < r.b := ble_false_gt hc2
      omega
    · have h1 : r.c - r.b < r.b - r.a := ble_false_gt hc1
      have h2 : r.b ≤ 18 - r.b := (Nat.ble_eq).mp hc2
      omega
    · have h1 : r.b - r.a ≤ r.c - r.b := (Nat.ble_eq).mp hc1
      have h2 : 18 - r.b < r.b := ble_false_gt hc2
      omega
    · have h1 : r.b - r.a ≤ r.c - r.b := (Nat.ble_eq).mp hc1
      have h2 : r.b ≤ 18 - r.b := (Nat.ble_eq).mp hc2
      omega
  have hbal : 3 * rectCharge r ≤
      rectDualMass suppPairs18 dual18 ⟨r.b - rectCharge r, r.b, r.b + rectCharge r, 1⟩ :=
    checkBalancedAtCenter_sound r.b (maxBalH18 r.b) (rectCharge r) hcenter hh1 hhmax
  have hw : rectDualMass suppPairs18 dual18 ⟨r.b - rectCharge r, r.b, r.b + rectCharge r, 1⟩ =
      rectDualMass suppPairs18 dual18 (balancedCore r) := by
    unfold balancedCore; rfl
  rw [hw] at hbal
  have hdom : rectDualMass suppPairs18 dual18 (balancedCore r) ≤ rectDualMass suppPairs18 dual18 r :=
    balanced_core_dualMass_le suppPairs18 dual18 r (Nat.le_of_lt hab) (Nat.le_of_lt hbc)
  exact Nat.le_trans hbal hdom

/--
MAIN UNIVERSAL N=18 UPPER-BOUND THEOREM:
For ANY adjacent-rectangle list `P` on `{0..18}` whose pair load at each of the 41 dual-support
pairs is `<= scale`, `3 * primalObj P <= 107 * scale` (so `primalObj P <= 107` when `scale = 3`).
-/
theorem n18_universal_optimum_upper_bound (scale : Nat) (P : List RectWeight)
    (hvalid : ∀ r, r ∈ P → r.a < r.b ∧ r.b < r.c ∧ r.c ≤ 18)
    (hcong : ∀ p, p ∈ suppPairs18 → pairLoad P p ≤ scale) :
    3 * primalObj P ≤ 107 * scale := by
  have hcov : ∀ r, r ∈ P → 3 * rectCharge r ≤ rectDualMass suppPairs18 dual18 r := by
    intro r hr
    obtain ⟨hab, hbc, hc18⟩ := hvalid r hr
    exact dual18_covers_every_valid_rect18 r hab hbc hc18
  have hsum : ∀ p, p ∈ suppPairs18 → dual18 p * pairLoad P p ≤ dual18 p * scale := by
    intro p hp
    exact Nat.mul_le_mul_left (dual18 p) (hcong p hp)
  have h1 : 3 * primalObj P ≤ weightedDualRectSum suppPairs18 dual18 P :=
    scale_primal_le_weighted_dual suppPairs18 dual18 3 P hcov
  rw [fubini_rect_pair_exchange] at h1
  have h2 : gridSum suppPairs18 (fun p => dual18 p * pairLoad P p) ≤
      gridSum suppPairs18 (fun p => dual18 p * scale) :=
    gridSum_mono suppPairs18 _ _ hsum
  rw [← gridSum_mul_right, dual18_total_mass_eq_107] at h2
  exact Nat.le_trans h1 h2

/-- Clean-room simplex-derived N=19 half-integral primal support (`34` rectangles, scaled by `2`). -/
def cleanRoomPrimal19 : List RectWeight := [
  ⟨0, 1, 2, 2⟩, ⟨0, 2, 4, 1⟩, ⟨0, 4, 8, 1⟩, ⟨0, 5, 10, 1⟩, ⟨0, 9, 18, 1⟩,
  ⟨1, 2, 3, 1⟩, ⟨1, 3, 5, 1⟩, ⟨1, 10, 19, 1⟩, ⟨2, 3, 4, 1⟩, ⟨3, 4, 5, 1⟩,
  ⟨4, 5, 6, 1⟩, ⟨4, 6, 8, 1⟩, ⟨5, 6, 7, 1⟩, ⟨5, 7, 9, 1⟩, ⟨6, 7, 8, 1⟩,
  ⟨6, 8, 10, 1⟩, ⟨7, 8, 9, 1⟩, ⟨8, 9, 10, 1⟩, ⟨9, 10, 11, 1⟩, ⟨9, 11, 13, 1⟩,
  ⟨9, 14, 19, 1⟩, ⟨10, 11, 12, 1⟩, ⟨10, 12, 14, 1⟩, ⟨11, 12, 13, 1⟩, ⟨11, 13, 15, 1⟩,
  ⟨11, 15, 19, 1⟩, ⟨12, 13, 14, 1⟩, ⟨13, 14, 15, 1⟩, ⟨14, 15, 16, 1⟩, ⟨14, 16, 18, 1⟩,
  ⟨15, 16, 17, 1⟩, ⟨15, 17, 19, 1⟩, ⟨16, 17, 18, 1⟩, ⟨17, 18, 19, 2⟩
]

theorem cleanRoomPrimal19_pair_congestion :
    ∀ i : Fin 19, ∀ j : Fin 19, i.val < j.val →
      pairLoad cleanRoomPrimal19 (i.val, j.val) ≤ 2 := by
  decide

theorem cleanRoomPrimal19_integer_gap_over_every_tree (t : IntervalTree) (ht : treeSize t = 19) :
    primalObj cleanRoomPrimal19 = 76 ∧ 2 * treeScore t + 2 ≤ primalObj cleanRoomPrimal19 := by
  have hub : treeScore t ≤ laminarTreeOpt 19 := by
    have h20 : treeSize t ≤ 20 := by omega
    have h1 := universal_laminar_tree_upper_bound t h20
    rw [ht] at h1
    exact h1
  have hval : primalObj cleanRoomPrimal19 = 76 ∧ laminarTreeOpt 19 = 37 := by decide
  exact ⟨hval.1, by omega⟩

/-- Diophantine 8-bank vs 2-bank decimal-identifier growth inequalities (`10^3 < 2^10 < 10^4`, `9 * 10^6 < 2^24 < 2 * 10^24`). -/
theorem eight_bank_diophantine_sublinearity :
    10 ^ 3 < 2 ^ 10 ∧ 2 ^ 10 < 10 ^ 4 ∧ 9 * (10 ^ 6) < 2 ^ 24 ∧ 2 ^ 24 < 2 * (10 ^ 24) := by
  decide

/-- Clean-room 5-clause degree->=3 port replacement gadget extension law over `{false, true}^3`. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

def fiveClauseSat (a b c x y z : Bool) : Bool :=
  (a || y || z) &&
  (b || x || !z) &&
  (c || !x || !y) &&
  (x || !y || z) &&
  (!x || y || !z)

def auxCube : List (Bool × Bool × Bool) := [
  (false, false, false), (false, false, true), (false, true, false), (false, true, true),
  (true, false, false), (true, false, true), (true, true, false), (true, true, true)
]

def fiveClauseExtCount (a b c : Bool) : Nat :=
  (auxCube.filter (fun t => fiveClauseSat a b c t.1 t.2.1 t.2.2)).length

theorem five_clause_gadget_exact_multiplicity :
    ∀ a b c : Bool, fiveClauseExtCount a b c = 2 * (b2n a + b2n b + b2n c) := by
  decide

end CleanRoomTimeCutDuality
