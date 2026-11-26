/-
  Erdős Problem #848 — Universal Zero-Sorry Lean 4 Proof for ALL `N ≤ 307`
  Verified with Vanilla Lean 4.36.0 Kernel (zero `sorry`, zero custom axioms).

  Proves unconditionally over ALL subsets `A` (`2^307` possibilities!):
    `theorem erdos848_universal_le_307 (N : Nat) (hN : N ≤ 307) (A : List Nat)`
    `    (h_nodup : A.Nodup) (h_range : ∀ a, a ∈ A → a < N)`
    `    (h_prop : ∀ a, a ∈ A → ∀ b, b ∈ A → ¬ IsSquarefree (a * b + 1)) :`
    `    A.length ≤ countA7 N`
-/

namespace Erdos848Proofs

/-- First-principles definition of squarefreeness: no integer `d ≥ 2` has `d^2 ∣ m`. -/
def IsSquarefree (m : Nat) : Prop :=
  ∀ d : Nat, 2 ≤ d → (m % (d * d) = 0 → False)

/-- Cardinality of `A_7(N) = {n < N : n % 25 = 7}`: -/
def countA7 (N : Nat) : Nat :=
  if N ≤ 7 then 0 else (N - 8) / 25 + 1

/-- Fast boolean checker for `IsSquarefree m`: checks `m % (d*d) != 0` for `2 ≤ d ≤ B` where `m < (B+1)^2`! -/
def noSquareDivUpTo (m : Nat) : Nat → Bool
  | 0 | 1 => true
  | d' + 1 =>
      let d := d' + 1
      ((m % (d * d)) != 0) && noSquareDivUpTo m d'

theorem noSquareDivUpTo_sound (m : Nat) :
    ∀ (B : Nat), noSquareDivUpTo m B = true → ∀ d, 2 ≤ d → d ≤ B → m % (d * d) = 0 → False
  | 0, _, d, hd2, hd0, _ => by omega
  | 1, _, d, hd2, hd1, _ => by omega
  | d' + 1, h, d, hd2, hdB, hmod => by
    cases d' with
    | zero => omega
    | succ d'' =>
      unfold noSquareDivUpTo at h
      simp only [Bool.and_eq_true, bne_iff_ne] at h
      by_cases heq : d = d'' + 2
      · subst heq
        exact h.1 hmod
      · exact noSquareDivUpTo_sound m (d'' + 1) h.2 d hd2 (by omega) hmod

def checkSqFreePos (m B : Nat) : Bool :=
  decide (0 < m) && decide (m < (B + 1) * (B + 1)) && noSquareDivUpTo m B

theorem checkSqFreePos_sound {m B : Nat} (h : checkSqFreePos m B = true) : IsSquarefree m := by
  unfold checkSqFreePos at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hm0, hmb⟩, hnd⟩ := h
  intro d hd2 hmod
  by_cases hdB : d ≤ B
  · exact noSquareDivUpTo_sound m B hnd d hd2 hdB hmod
  · have hd_ge : B + 1 ≤ d := by omega
    have hsq_ge : (B + 1) * (B + 1) ≤ d * d := Nat.mul_le_mul hd_ge hd_ge
    have hlt : m < d * d := Nat.lt_of_lt_of_le hmb hsq_ge
    have hm_eq : m % (d * d) = m := Nat.mod_eq_of_lt hlt
    omega

-- ============================================================================
-- PIGEONHOLE INJECTION INTO `Fin K` (ZERO SORRY)
-- ============================================================================

theorem erase_length_succ {α : Type} [DecidableEq α] (x : α) :
    ∀ (ys : List α), x ∈ ys → (ys.erase x).length + 1 = ys.length
  | [], hx => by cases hx
  | y :: rest, hx => by
    simp only [List.erase_cons]
    by_cases hyx : (y == x) = true
    · rw [hyx]; simp
    · have hyx_ne : y ≠ x := fun heq => hyx (beq_iff_eq.mpr heq)
      have hf : (y == x) = false := Bool.eq_false_iff.mpr hyx
      rw [hf]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      cases hx with
      | head => exact absurd rfl hyx_ne
      | tail _ hm =>
        have ih := erase_length_succ x rest hm
        omega

theorem nodup_sublist_length_le {α : Type} [DecidableEq α] :
    ∀ (xs univ : List α), xs.Nodup → (∀ u, u ∈ xs → u ∈ univ) → xs.length ≤ univ.length
  | [], _, _, _ => by simp
  | x :: xs, univ, hnd, hsub => by
    have ⟨hx_not, hxs_nd⟩ := List.nodup_cons.mp hnd
    have hx_in : x ∈ univ := hsub x (List.mem_cons_self ..)
    have hsub_er : ∀ u, u ∈ xs → u ∈ univ.erase x := by
      intro u hu
      have hu_in := hsub u (List.mem_cons_of_mem x hu)
      have hne : u ≠ x := fun heq => hx_not (heq ▸ hu)
      exact (List.mem_erase_of_ne hne).mpr hu_in
    have ih := nodup_sublist_length_le xs (univ.erase x) hxs_nd hsub_er
    have her := erase_length_succ x univ hx_in
    simp only [List.length_cons]
    omega

theorem nodup_map_of_inj_on {α β : Type} (f : α → β) :
    ∀ (xs : List α), xs.Nodup → (∀ a, a ∈ xs → ∀ b, b ∈ xs → a ≠ b → f a ≠ f b) → (xs.map f).Nodup
  | [], _, _ => List.Pairwise.nil
  | x :: xs, hnd, hinj => by
    have ⟨hx_not, hxs_nd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj_on f xs hxs_nd (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨y, hy_in, hfy⟩ := hmem
    have hyx : y ≠ x := fun heq => hx_not (heq ▸ hy_in)
    exact hinj y (List.mem_cons_of_mem x hy_in) x (List.mem_cons_self ..) hyx hfy

theorem length_le_of_inj_to_fin {K : Nat} (A : List Nat) (hnd : A.Nodup)
    (f : Nat → Fin K)
    (hinj : ∀ a, a ∈ A → ∀ b, b ∈ A → a ≠ b → f a ≠ f b) :
    A.length ≤ K := by
  have hmap_nd : (A.map f).Nodup := nodup_map_of_inj_on f A hnd hinj
  have hle := nodup_sublist_length_le (A.map f) (List.finRange K) hmap_nd (fun u _ => List.mem_finRange u)
  rw [List.length_map, List.length_finRange] at hle
  exact hle

-- ============================================================================
-- EMBEDDED DUAL K-COLORING CERTIFICATES FOR ALL 0 ≤ N ≤ 307
-- ============================================================================

def validVal (i : Nat) : Nat :=
  (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 7 else 18) else (if Nat.ble i 2 then 32 else 38)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 41 else 43) else (if Nat.ble i 6 then 57 else 68))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 70 else 82) else (if Nat.ble i 10 then 93 else 99)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 107 else 117) else (if Nat.ble i 14 then 118 else 132)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 143 else 157) else (if Nat.ble i 18 then 168 else 182)) else (if Nat.ble i 21 then (if Nat.ble i 20 then 193 else 207) else (if Nat.ble i 22 then 218 else 232))) else (if Nat.ble i 27 then (if Nat.ble i 25 then (if Nat.ble i 24 then 239 else 243) else (if Nat.ble i 26 then 251 else 257)) else (if Nat.ble i 29 then (if Nat.ble i 28 then 268 else 282) else 293))))
def validIdx (a : Nat) : Nat :=
  (if Nat.ble a 153 then (if Nat.ble a 76 then (if Nat.ble a 38 then (if Nat.ble a 19 then (if Nat.ble a 9 then (if Nat.ble a 4 then 31 else (if Nat.ble a 7 then (if Nat.ble a 6 then 31 else 0) else 31)) else (if Nat.ble a 14 then 31 else (if Nat.ble a 17 then 31 else (if Nat.ble a 18 then 1 else 31)))) else (if Nat.ble a 29 then 31 else (if Nat.ble a 34 then (if Nat.ble a 32 then (if Nat.ble a 31 then 31 else 2) else 31) else (if Nat.ble a 36 then 31 else (if Nat.ble a 37 then 31 else 3))))) else (if Nat.ble a 57 then (if Nat.ble a 48 then (if Nat.ble a 43 then (if Nat.ble a 41 then (if Nat.ble a 40 then 31 else 4) else (if Nat.ble a 42 then 31 else 5)) else 31) else (if Nat.ble a 53 then 31 else (if Nat.ble a 55 then 31 else (if Nat.ble a 56 then 31 else 6)))) else (if Nat.ble a 67 then 31 else (if Nat.ble a 72 then (if Nat.ble a 70 then (if Nat.ble a 69 then (if Nat.ble a 68 then 7 else 31) else 8) else 31) else 31)))) else (if Nat.ble a 115 then (if Nat.ble a 96 then (if Nat.ble a 86 then (if Nat.ble a 81 then 31 else (if Nat.ble a 84 then (if Nat.ble a 83 then (if Nat.ble a 82 then 9 else 31) else 31) else 31)) else (if Nat.ble a 91 then 31 else (if Nat.ble a 94 then (if Nat.ble a 93 then (if Nat.ble a 92 then 31 else 10) else 31) else 31))) else (if Nat.ble a 106 then (if Nat.ble a 101 then (if Nat.ble a 99 then (if Nat.ble a 98 then 31 else 11) else 31) else 31) else (if Nat.ble a 111 then (if Nat.ble a 109 then (if Nat.ble a 108 then (if Nat.ble a 107 then 12 else 31) else 31) else 31) else 31))) else (if Nat.ble a 134 then (if Nat.ble a 125 then (if Nat.ble a 120 then (if Nat.ble a 118 then (if Nat.ble a 117 then (if Nat.ble a 116 then 31 else 13) else 14) else 31) else 31) else (if Nat.ble a 130 then 31 else (if Nat.ble a 132 then (if Nat.ble a 131 then 31 else 15) else 31))) else (if Nat.ble a 144 then (if Nat.ble a 139 then 31 else (if Nat.ble a 142 then 31 else (if Nat.ble a 143 then 16 else 31))) else 31)))) else (if Nat.ble a 230 then (if Nat.ble a 192 then (if Nat.ble a 173 then (if Nat.ble a 163 then (if Nat.ble a 158 then (if Nat.ble a 156 then 31 else (if Nat.ble a 157 then 17 else 31)) else 31) else (if Nat.ble a 168 then (if Nat.ble a 166 then 31 else (if Nat.ble a 167 then 31 else 18)) else 31)) else (if Nat.ble a 183 then (if Nat.ble a 178 then 31 else (if Nat.ble a 181 then 31 else (if Nat.ble a 182 then 19 else 31))) else 31)) else (if Nat.ble a 211 then (if Nat.ble a 202 then (if Nat.ble a 197 then (if Nat.ble a 195 then (if Nat.ble a 194 then (if Nat.ble a 193 then 20 else 31) else 31) else 31) else 31) else (if Nat.ble a 207 then (if Nat.ble a 205 then 31 else (if Nat.ble a 206 then 31 else 21)) else 31)) else (if Nat.ble a 221 then (if Nat.ble a 216 then 31 else (if Nat.ble a 219 then (if Nat.ble a 218 then (if Nat.ble a 217 then 31 else 22) else 31) else 31)) else 31))) else (if Nat.ble a 268 then (if Nat.ble a 249 then (if Nat.ble a 240 then (if Nat.ble a 235 then (if Nat.ble a 233 then (if Nat.ble a 232 then (if Nat.ble a 231 then 31 else 23) else 31) else 31) else (if Nat.ble a 238 then 31 else (if Nat.ble a 239 then 24 else 31))) else (if Nat.ble a 245 then (if Nat.ble a 243 then (if Nat.ble a 242 then 31 else 25) else 31) else 31)) else (if Nat.ble a 259 then (if Nat.ble a 254 then (if Nat.ble a 252 then (if Nat.ble a 251 then (if Nat.ble a 250 then 31 else 26) else 31) else 31) else (if Nat.ble a 257 then (if Nat.ble a 256 then 31 else 27) else 31)) else (if Nat.ble a 264 then 31 else (if Nat.ble a 266 then 31 else (if Nat.ble a 267 then 31 else 28))))) else (if Nat.ble a 287 then (if Nat.ble a 278 then 31 else (if Nat.ble a 283 then (if Nat.ble a 281 then 31 else (if Nat.ble a 282 then 29 else 31)) else 31)) else (if Nat.ble a 297 then (if Nat.ble a 292 then 31 else (if Nat.ble a 295 then (if Nat.ble a 294 then (if Nat.ble a 293 then 30 else 31) else 31) else 31)) else 31)))))
def colTable (K i : Nat) : Nat :=
  (if Nat.ble K 6 then (if Nat.ble K 3 then (if Nat.ble K 1 then (if Nat.ble K 0 then 0 else 0) else (if Nat.ble K 2 then (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 1) else (if Nat.ble i 2 then 1 else 0)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 1 else 0) else 0)) else 0) else 0) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 2) else (if Nat.ble i 2 then 1 else 2)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 1 else 0) else (if Nat.ble i 6 then 2 else 1))) else 0) else 0))) else (if Nat.ble K 5 then (if Nat.ble K 4 then (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 2) else (if Nat.ble i 2 then 1 else 3)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 2 else 0) else (if Nat.ble i 6 then 2 else 1))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 0 else 3) else (if Nat.ble i 10 then 3 else 0)) else 0)) else 0) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then 0 else (if Nat.ble i 2 then 1 else 3)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 1 else 3) else (if Nat.ble i 6 then 2 else 4))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 2 else 3) else (if Nat.ble i 10 then 2 else 3)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 1) else (if Nat.ble i 14 then 1 else 0)))) else 0)) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 2) else (if Nat.ble i 2 then 1 else 5)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 2 else 4) else (if Nat.ble i 6 then 2 else 1))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 0 else 3) else (if Nat.ble i 10 then 3 else 0)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 1) else (if Nat.ble i 14 then 0 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 5 else 0) else 0) else 0) else 0)))) else (if Nat.ble K 9 then (if Nat.ble K 8 then (if Nat.ble K 7 then (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 6) else (if Nat.ble i 2 then 1 else 5)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 6 else 3) else (if Nat.ble i 6 then 2 else 4))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 0 else 3) else (if Nat.ble i 10 then 5 else 0)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 2) else (if Nat.ble i 14 then 0 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 1 else 6) else (if Nat.ble i 18 then 2 else 0)) else 0) else 0)) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 2) else (if Nat.ble i 2 then 1 else 7)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 6 else 4) else (if Nat.ble i 6 then 2 else 6))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 4 else 3) else (if Nat.ble i 10 then 1 else 3)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 6) else (if Nat.ble i 14 then 3 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 0 else 6) else 7) else (if Nat.ble i 21 then (if Nat.ble i 20 then 5 else 0) else 0)) else 0))) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 4) else 1) else (if Nat.ble i 5 then (if Nat.ble i 4 then 2 else 8) else (if Nat.ble i 6 then 2 else 5))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 8 else 3) else (if Nat.ble i 10 then 7 else 8)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 5) else (if Nat.ble i 14 then 6 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 0 else 6) else (if Nat.ble i 18 then 3 else 7)) else (if Nat.ble i 21 then (if Nat.ble i 20 then 2 else 8) else (if Nat.ble i 22 then 1 else 0))) else 0))) else (if Nat.ble K 11 then (if Nat.ble K 10 then (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 2) else (if Nat.ble i 2 then 1 else 8)) else (if Nat.ble i 5 then (if Nat.ble i 4 then 2 else 4) else (if Nat.ble i 6 then 2 else 5))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 4 else 3) else (if Nat.ble i 10 then 1 else 9)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 7) else (if Nat.ble i 14 then 8 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 0 else 6) else 7) else (if Nat.ble i 21 then (if Nat.ble i 20 then 6 else 8) else 9)) else (if Nat.ble i 27 then (if Nat.ble i 25 then 3 else (if Nat.ble i 26 then 4 else 0)) else 0))) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 5) else 1) else (if Nat.ble i 5 then (if Nat.ble i 4 then 1 else 9) else (if Nat.ble i 6 then 2 else 6))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 0 else 3) else (if Nat.ble i 10 then 7 else 9)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 3) else (if Nat.ble i 14 then 8 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 0 else 6) else (if Nat.ble i 18 then 3 else 7)) else (if Nat.ble i 21 then (if Nat.ble i 20 then 10 else 8) else (if Nat.ble i 22 then 1 else 9))) else (if Nat.ble i 27 then (if Nat.ble i 25 then (if Nat.ble i 24 then 5 else 4) else (if Nat.ble i 26 then 4 else 10)) else (if Nat.ble i 29 then (if Nat.ble i 28 then 2 else 0) else 0))))) else (if Nat.ble i 15 then (if Nat.ble i 7 then (if Nat.ble i 3 then (if Nat.ble i 1 then (if Nat.ble i 0 then 0 else 8) else 1) else (if Nat.ble i 5 then (if Nat.ble i 4 then 6 else 0) else (if Nat.ble i 6 then 2 else 11))) else (if Nat.ble i 11 then (if Nat.ble i 9 then (if Nat.ble i 8 then 4 else 3) else (if Nat.ble i 10 then 5 else 9)) else (if Nat.ble i 13 then (if Nat.ble i 12 then 4 else 10) else (if Nat.ble i 14 then 6 else 5)))) else (if Nat.ble i 23 then (if Nat.ble i 19 then (if Nat.ble i 17 then (if Nat.ble i 16 then 9 else 6) else (if Nat.ble i 18 then 1 else 7)) else (if Nat.ble i 21 then (if Nat.ble i 20 then 2 else 8) else (if Nat.ble i 22 then 10 else 9))) else (if Nat.ble i 27 then (if Nat.ble i 25 then (if Nat.ble i 24 then 11 else 4) else (if Nat.ble i 26 then 7 else 10)) else (if Nat.ble i 29 then (if Nat.ble i 28 then 7 else 11) else 3)))))))

/-- Verify for ALL `a < 307`: either `validIdx a < 31 ∧ validVal (validIdx a) = a`,
    OR `a^2 + 1` is strictly squarefree (`checkSqFreePos (a*a + 1) a = true`)! -/
def checkSelfValidFilter : Bool :=
  (List.finRange 307).all fun a =>
    let idx := validIdx a.val
    if idx < 31 then
      validVal idx == a.val
    else
      checkSqFreePos (a.val * a.val + 1) (a.val + 1)

/-- Verify for ALL endpoints `K ∈ {1..12}` (`N_K = 7 + 25 * K`):
    1) Every `i < 31` with `validVal i < 7 + 25 * K` has `colTable K i < K`, and
    2) Every pair `j < i < 31` with both `< 7 + 25 * K` and `colTable K j == colTable K i`
       has `(validVal j) * (validVal i) + 1` STRICTLY SQUAREFREE! -/
def checkAllEndpointColorings : Bool :=
  (List.finRange 13).all fun Kf =>
    let K := Kf.val
    if K == 0 then true
    else
      let NK := 7 + 25 * K
      let vs := List.finRange 31
      (vs.all fun i =>
        !(validVal i.val < NK) || decide (colTable K i.val < K)) &&
      (vs.all fun i =>
        vs.all fun j =>
          !(j.val < i.val && validVal i.val < NK && validVal j.val < NK && colTable K j.val == colTable K i.val) ||
          checkSqFreePos (validVal j.val * validVal i.val + 1) 307)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem selfValidFilter_ok : checkSelfValidFilter = true := by decide
theorem allEndpointColorings_ok : checkAllEndpointColorings = true := by decide

theorem a_in_valid_of_not_sqfree {a : Nat} (ha : a < 307)
    (hnsq : ¬ IsSquarefree (a * a + 1)) :
    validIdx a < 31 ∧ validVal (validIdx a) = a := by
  have h := selfValidFilter_ok
  unfold checkSelfValidFilter at h
  let fa : Fin 307 := ⟨a, ha⟩
  have ha_ok := (List.all_eq_true.mp h) fa (List.mem_finRange fa)
  have hfa_val : fa.val = a := rfl
  rw [hfa_val] at ha_ok
  by_cases hlt : validIdx a < 31
  · simp [hlt] at ha_ok
    exact ⟨hlt, ha_ok⟩
  · simp [hlt] at ha_ok
    exfalso
    exact hnsq (checkSqFreePos_sound ha_ok)

theorem countA7_endpoint_bound (N : Nat) : N ≤ 7 + 25 * countA7 N := by
  unfold countA7
  by_cases h7 : N ≤ 7
  · simp [h7]
  · simp [h7]; omega

/-- **MAIN UNIVERSAL THEOREM (Erdős #848 for ALL `0 ≤ N ≤ 307`, ZERO `sorry`)**:
    For every `N ≤ 307` and every duplicate-free subset `A ⊆ {0, ..., N - 1}` such that
    `a * b + 1` is never squarefree for `a, b ∈ A`, `|A| ≤ |A_7(N)|`! -/
theorem erdos848_universal_le_307 (N : Nat) (hN : N ≤ 307) (A : List Nat)
    (h_nodup : A.Nodup)
    (h_range : ∀ a, a ∈ A → a < N)
    (h_prop : ∀ a, a ∈ A → ∀ b, b ∈ A → ¬ IsSquarefree (a * b + 1)) :
    A.length ≤ countA7 N := by
  let K := countA7 N
  have hNK : N ≤ 7 + 25 * K := countA7_endpoint_bound N
  have hK_le : K ≤ 12 := by
    show countA7 N ≤ 12
    unfold countA7
    by_cases h7 : N ≤ 7 <;> simp [h7] <;> omega
  by_cases hK0 : K = 0
  · -- When K = 0, `N ≤ 7`, so `A` must be empty because every `a < 7` has `a^2 + 1` squarefree!
    cases A with
    | nil => simp
    | cons a rest =>
      exfalso
      have haN : a < N := h_range a (List.mem_cons_self ..)
      have ha7 : a < 7 := by omega
      have ⟨hidx, hval⟩ := a_in_valid_of_not_sqfree (by omega) (h_prop a (List.mem_cons_self ..) a (List.mem_cons_self ..))
      -- But `validVal 0 = 7` is the minimum of `validVal`! Let's check `validVal i ≥ 7` via `a < 7`!
      -- Even simpler: check directly for `a < 7` that `IsSquarefree (a*a + 1)`!
      have h7_sq : ∀ x : Fin 7, checkSqFreePos (x.val * x.val + 1) 7 = true := by decide
      exact h_prop a (List.mem_cons_self ..) a (List.mem_cons_self ..) (checkSqFreePos_sound (h7_sq ⟨a, ha7⟩))
  · -- When `1 ≤ K ≤ 12`: map each `a ∈ A` to `⟨colTable K (validIdx a), ...⟩ : Fin K`!
    have h_all := allEndpointColorings_ok
    unfold checkAllEndpointColorings at h_all
    let Kf : Fin 13 := ⟨K, by omega⟩
    have hKf := (List.all_eq_true.mp h_all) Kf (List.mem_finRange Kf)
    have hKf_val : Kf.val = K := rfl
    rw [hKf_val] at hKf
    have hK0_b : (K == 0) = false := beq_eq_false_iff_ne.mpr hK0
    simp only [hK0_b, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hKf
    obtain ⟨h_col_bound, h_pairs⟩ := hKf
    -- Helper: for any `a ∈ A`, `colTable K (validIdx a) < K`
    have h_mem_col : ∀ a, a ∈ A → colTable K (validIdx a) < K := by
      intro a ha
      have haM : a < 307 := Nat.lt_of_lt_of_le (h_range a ha) hN
      have ⟨hidx, hval⟩ := a_in_valid_of_not_sqfree haM (h_prop a ha a ha)
      have hi := (List.all_eq_true.mp h_col_bound) ⟨validIdx a, hidx⟩ (List.mem_finRange _)
      change (!decide (validVal (validIdx a) < 7 + 25 * K) || decide (colTable K (validIdx a) < K)) = true at hi
      have haNK : validVal (validIdx a) < 7 + 25 * K := by rw [hval]; exact Nat.lt_of_lt_of_le (h_range a ha) hNK
      simp [haNK] at hi
      exact hi
    -- Define total function `f : Nat → Fin K` (defaulting to `0` outside `A`):
    have hK_pos : 0 < K := by omega
    let f : Nat → Fin K := fun a =>
      if h : colTable K (validIdx a) < K then ⟨colTable K (validIdx a), h⟩ else ⟨0, hK_pos⟩
    apply length_le_of_inj_to_fin A h_nodup f
    intro a ha b hb hab heq
    have hca := h_mem_col a ha
    have hcb := h_mem_col b hb
    simp only [f, hca, hcb, ↓reduceDIte, Fin.mk.injEq] at heq
    have haM : a < 307 := Nat.lt_of_lt_of_le (h_range a ha) hN
    have hbM : b < 307 := Nat.lt_of_lt_of_le (h_range b hb) hN
    have ⟨ia_lt, ia_val⟩ := a_in_valid_of_not_sqfree haM (h_prop a ha a ha)
    have ⟨ib_lt, ib_val⟩ := a_in_valid_of_not_sqfree hbM (h_prop b hb b hb)
    have hia_ne_ib : validIdx a ≠ validIdx b := by
      intro h_eq_i
      have : validVal (validIdx a) = validVal (validIdx b) := congrArg validVal h_eq_i
      rw [ia_val, ib_val] at this
      exact hab this
    by_cases hlt_i : validIdx a < validIdx b
    · have hi1 := (List.all_eq_true.mp h_pairs) ⟨validIdx b, ib_lt⟩ (List.mem_finRange _)
      have hi2 := (List.all_eq_true.mp hi1) ⟨validIdx a, ia_lt⟩ (List.mem_finRange _)
      change (!(decide (validIdx a < validIdx b) && decide (validVal (validIdx b) < 7 + 25 * K) && decide (validVal (validIdx a) < 7 + 25 * K) && (colTable K (validIdx a) == colTable K (validIdx b))) || checkSqFreePos (validVal (validIdx a) * validVal (validIdx b) + 1) 307) = true at hi2
      have hbNK : validVal (validIdx b) < 7 + 25 * K := by rw [ib_val]; exact Nat.lt_of_lt_of_le (h_range b hb) hNK
      have haNK : validVal (validIdx a) < 7 + 25 * K := by rw [ia_val]; exact Nat.lt_of_lt_of_le (h_range a ha) hNK
      have hcol_eq : (colTable K (validIdx a) == colTable K (validIdx b)) = true := beq_iff_eq.mpr heq
      simp [hlt_i, hbNK, haNK, hcol_eq] at hi2
      have hsq := checkSqFreePos_sound hi2
      rw [ia_val, ib_val] at hsq
      exact h_prop a ha b hb hsq
    · have hgt_i : validIdx b < validIdx a := by omega
      have hi1 := (List.all_eq_true.mp h_pairs) ⟨validIdx a, ia_lt⟩ (List.mem_finRange _)
      have hi2 := (List.all_eq_true.mp hi1) ⟨validIdx b, ib_lt⟩ (List.mem_finRange _)
      change (!(decide (validIdx b < validIdx a) && decide (validVal (validIdx a) < 7 + 25 * K) && decide (validVal (validIdx b) < 7 + 25 * K) && (colTable K (validIdx b) == colTable K (validIdx a))) || checkSqFreePos (validVal (validIdx b) * validVal (validIdx a) + 1) 307) = true at hi2
      have haNK : validVal (validIdx a) < 7 + 25 * K := by rw [ia_val]; exact Nat.lt_of_lt_of_le (h_range a ha) hNK
      have hbNK : validVal (validIdx b) < 7 + 25 * K := by rw [ib_val]; exact Nat.lt_of_lt_of_le (h_range b hb) hNK
      have hcol_eq : (colTable K (validIdx b) == colTable K (validIdx a)) = true := beq_iff_eq.mpr heq.symm
      simp [hgt_i, haNK, hbNK, hcol_eq] at hi2
      have hsq := checkSqFreePos_sound hi2
      rw [ib_val, ia_val] at hsq
      exact h_prop b hb a ha hsq

-- Verify ZERO `sorry` and ZERO custom axioms:
#print axioms erdos848_universal_le_307

end Erdos848Proofs
