import Std.Data.Nat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Complex.Exponential


opaque Garbage : Nat

/--
 https://en.wikipedia.org/wiki/Knuth%27s_up-arrow_notation#Definition
-/
def Knuth (a : Nat) (n : Nat) (b : Nat) : Nat :=
  match n, b with
  /-
  This is a garbage value but in proofs we limit ourselves to n > 0,
  similar to Nat.add.
  I was told to use this instead of a subtype to show that we can prove
  0 < n without being over eager about unfolding.
  -/
  | 0, _ => Garbage
  | 1, _ => a ^ b
  | _ + 2, 0 => 1
  | m + 2, b' + 1 =>
    let bNext := Knuth a (m + 2) b'
    Knuth a (m + 1) bNext
termination_by Knuth a n b => (n, b)


theorem Knuth.pos_of_pos (a b n : Nat) (ha : 0 < a) (hn : 0 < n) : 0 < Knuth a n b := by
  /-
  Since Knuth recurses in a non standard way, the way that we do induction
  here should be the same non standard scheme so our induction closely
  matches the actual behavior of the function
  -/
  match n, b with
  /-
  0 is impossible due to hn
  -/
  | 0, _ => contradiction
  /-
  This is trivially true since the base is greater than 0
  -/
  | 1, _ => simp [Knuth, Nat.pos_pow_of_pos, ha]
  /-
  This is trivially true per definition
  -/
  | m + 2, 0 => simp [Knuth]
  /-
  This is our inductive/recursive case. Since we used match instead of induction
  we have to do "manual induction" by doing recursion with the theorem itself
  -/
  | m + 2, b' + 1 =>
    rw [Knuth]
    apply Knuth.pos_of_pos <;> simp_all_arith

/--
The g function from: https://en.wikipedia.org/wiki/Graham%27s_number.
-/
def g (n : Nat) : Nat :=
  match n with
  | 0 => Knuth 3 4 3
  | m + 1 => Knuth 3 (g m) 3

/--
g is just defined via "normal" recursion on Nat so we just use "normal" induction.
-/
theorem g_pos (n : Nat) : 0 < g n := by
  induction n with
  | zero =>
    rw [g]
    apply Knuth.pos_of_pos <;> simp_arith
  | succ m ih =>
    rw [g]
    apply Knuth.pos_of_pos
    · simp_arith
    · assumption

/--
Graham's number from: https://en.wikipedia.org/wiki/Graham%27s_number.
-/
def G : Nat := g 63

theorem G_pos : 0 < G := by apply g_pos

/-
The proof from here on is mostly an automated version of the corresponding agda proof.
-/

notation:60 a:61 " ↑ " b:62 => Knuth a 1 b
notation:60 a:61 " ↑↑ " b:62 => Knuth a 2 b

theorem Level1 (n : Nat) : (3 ↑ n) % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Knuth] at ih
    simp [Knuth, ih, Nat.pow_succ, Nat.mul_mod]

/--
As we will see there are a couple of proofs below
that get all resolved by unfolding the definition
of Knuth and calling ring on it so we define a shorthand.
-/
macro "knuth_ring" : tactic => `(tactic| simp only [Knuth] <;> ring_nf)

theorem Level2 (n : Nat) (h : n % 2 = 1) : (3 ↑ n) % 4 = 3 := by
  match n with
  | 1 => rfl
  | m + 2 =>
    calc
      (3 ↑ m + 2) % 4 = 3 * (3 * (3 ↑ m)) % 4 := by knuth_ring
      _ = 9 * (3 ↑ m) % 4 := by knuth_ring
      _ = (3 ↑ m) % 4 := by
        rw [Nat.mul_mod]
        norm_num
      _ = 3 := by
        apply Level2
        norm_num at h
        assumption

theorem Level3 (n : Nat) (h : n % 4 = 3) : (3 ↑ n) % 10 = 7 := by
  match n with
  | 3 => rfl
  | m + 4 =>
    calc
      (3 ↑ m + 4) % 10 = 3 * (3 ↑ (3 + m))  % 10 := by knuth_ring
      _ = 81 * (3 ↑ m) % 10 := by knuth_ring
      _ = ((3 ↑ m) % 10) % 10 := by
        rw [Nat.mul_mod]
        norm_num
      _ = (3 ↑ m) % 10 := by rw [Nat.mod_mod]
      _ = 7 := by
        apply Level3
        norm_num at h
        assumption

theorem Knuth_mod_10_eq_7 (n : Nat) : (3 ↑ (3 ↑ (3 ↑ n))) % 10 = 7 := by
  apply Level3
  apply Level2
  apply Level1

def HasThreeLevels (n : Nat) : Prop :=
  ∃ (m : Nat), n = (3 ↑ (3 ↑ (3 ↑ m)))

theorem mod_10_eq_7_of_HasThreeLevels (n : Nat) (h : HasThreeLevels n) : n % 10 = 7 := by
  cases h with
  | intro m hm => simp [hm, Knuth_mod_10_eq_7]

theorem ThreeLevels_finder_1 (n : Nat) (h : 3 ≤ n) : HasThreeLevels (Knuth 3 2 n) := by
  match n with
  | m + 3 =>
    exists 3 ↑↑ m
    simp [Knuth]

theorem three_le_Knuth_three (m n : Nat) (h1 : 0 < n) (h2 : 0 < m) : 3 ≤ Knuth 3 m n := by
  match m, n with
  | 0, n => contradiction
  | 1, n + 1 =>
    simp only [Knuth, Nat.pow_succ]
    /-
    This one can easily be found with loogle:
    |- (?n : Nat) <= ?m * ?n
    -/
    apply Nat.le_mul_of_pos_left
    simp_arith
  | m + 2, n + 1 =>
    simp only [Knuth]
    apply three_le_Knuth_three
    · apply Knuth.pos_of_pos <;> simp_arith
    · simp_arith

theorem three_le_g (n : Nat) : 3 ≤ g n := by
  cases n with
  | zero =>
    rw [g]
    apply three_le_Knuth_three <;> simp_arith
  | succ n =>
    simp only [g]
    apply three_le_Knuth_three
    · simp_arith
    · apply g_pos

theorem ThreeLevels_finder_2  (m n : Nat) (hm : 2 ≤ m) (hn : 3 ≤ n) : HasThreeLevels (Knuth 3 m n) := by
  match m, n with
  | 2, n =>
    apply ThreeLevels_finder_1
    assumption
  | m + 3, n + 1 =>
    simp only [Knuth]
    apply ThreeLevels_finder_2
    · simp_arith
    · apply three_le_Knuth_three
      · linarith
      · simp_arith

theorem G_HasThreeLevels : HasThreeLevels G := by
  rw [G]
  apply ThreeLevels_finder_2
  · refine Nat.le_trans ?_ (three_le_g _)
    simp_arith
  · simp_arith

theorem G_mod_10_eq_7 : G % 10 = 7 := by
  apply mod_10_eq_7_of_HasThreeLevels
  exact G_HasThreeLevels
